use std::{
    convert::{TryFrom, TryInto},
    fmt::Display,
    path::PathBuf,
    sync::atomic::Ordering,
};

use chrono::{DateTime, FixedOffset};
use clap::ArgMatches;
use flate2::bufread::GzDecoder;
use indicatif::{ProgressBar, ProgressStyle};
use reqwest::IntoUrl;
use tar::Archive;

use crate::{error, CliConfig, HostType};

static APP_USER_AGENT: &str = concat!(env!("CARGO_PKG_NAME"), "/", env!("CARGO_PKG_VERSION"),);

#[derive(PartialEq, Eq, Clone, Copy)]
enum QuillVersion {
    /// A nightly `quill` installation is uniquely characterised by its date and time of release.
    Nightly(DateTime<FixedOffset>),
}

impl Display for QuillVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuillVersion::Nightly(date) => write!(f, "nightly-{}", date.to_rfc3339()),
        }
    }
}

impl TryFrom<String> for QuillVersion {
    type Error = String;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        match DateTime::parse_from_rfc3339(&value.trim().replace(' ', "T")) {
            Ok(date) => Ok(QuillVersion::Nightly(date)),
            Err(err) => Err(format!("version string was not a valid date: {}", err)),
        }
    }
}

pub async fn process_update(cli_config: &CliConfig, _args: &ArgMatches<'_>) {
    if let crate::CompilerLocation::Installed { host, root } = &cli_config.compiler_location {
        eprintln!("checking latest version...",);
        let version: QuillVersion = download_text_or_exit(
            "https://github.com/quill-lang/quill/releases/download/latest-release/version.txt",
        )
        .await
        .try_into()
        .unwrap_or_else(|e| error(e));
        eprintln!("installing quill {}", version);

        download_self(*host, version).await;

        // Download components such as quillc.
        tokio::fs::create_dir_all(root.join("compiler-deps"))
            .await
            .unwrap();
        for component in &["quillc", "quill_lsp"] {
            download_artifact(
                &format!("{}_{}", host.component_prefix(), component),
                component,
                Some(version),
                root.join(component),
                false,
            )
            .await;
        }

        // Download development components such as dev-linux and target-linux.
        let dev_component = match host {
            HostType::Linux => "dev-linux",
            HostType::Windows => "dev-win",
        };

        download_artifact(
            dev_component,
            dev_component,
            None,
            root.join("compiler-deps"),
            true,
        )
        .await;

        for component in &["target-linux", "target-win"] {
            download_artifact(component, component, None, root.join("compiler-deps"), true).await;
        }
    } else {
        error("cannot update quill when running from source")
    }
}

async fn download_text_or_exit<U: IntoUrl>(url: U) -> String {
    let response = match reqwest::Client::builder()
        .user_agent(APP_USER_AGENT)
        .build()
        .unwrap()
        .get(url)
        .send()
        .await
    {
        Ok(response) => response,
        Err(_) => error("could not fetch quill version (could not connect to server)"),
    };

    if !response.status().is_success() {
        error(format!(
            "could not fetch quill version (connected but server returned error code '{}')",
            response.status()
        ))
    }

    match response.text().await {
        Ok(text) => text,
        Err(_) => {
            error("could not fetch quill version (connected but could not retrieve response body)")
        }
    }
}

/// If a version is provided, this function assumes that the tarball contains a `version.txt` file, and that the version should match the given expected version.
async fn download_tar_gz_or_exit<U: IntoUrl>(
    url: U,
    display_name: &str,
    dir: PathBuf,
    expected_version: Option<QuillVersion>,
) {
    let mut response = match reqwest::Client::builder()
        .user_agent(APP_USER_AGENT)
        .build()
        .unwrap()
        .get(url)
        .send()
        .await
    {
        Ok(response) => response,
        Err(_) => error(format!(
            "could not download {} (could not connect to server)",
            display_name
        )),
    };

    if !response.status().is_success() {
        error(format!(
            "could not download {} (connected but server returned error code '{}')",
            display_name,
            response.status()
        ))
    }

    let length = response.content_length().unwrap();
    let progress_bar = ProgressBar::new(length);
    progress_bar.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:30.cyan/blue}] {bytes}/{total_bytes} ({eta}) {msg}")
        .progress_chars("#>-")
    );
    progress_bar.set_message(format!("{} downloading", display_name));

    let mut bytes = Vec::new();

    loop {
        match response.chunk().await {
            Ok(Some(more_bytes)) => {
                progress_bar.inc(more_bytes.len() as u64);
                bytes.extend(more_bytes);
            }
            Ok(None) => {
                break;
            }
            Err(_) => error(format!(
                "could not download {} (connected but could not retrieve response body)",
                display_name
            )),
        }
    }

    progress_bar.set_message(format!("{} unpacking", display_name));
    let done = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));

    let done2 = std::sync::Arc::clone(&done);
    let dir2 = dir.clone();
    tokio::task::spawn_blocking(move || {
        let mut archive = Archive::new(GzDecoder::new(bytes.as_slice()));
        archive.unpack(dir2).unwrap();
        done2.store(true, Ordering::SeqCst);
    });

    while !done.load(Ordering::SeqCst) {
        progress_bar.tick();
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    }

    // Check the version.
    if let Some(expected_version) = expected_version {
        let version = tokio::fs::read_to_string(dir.join("version.txt"))
            .await
            .unwrap();
        let version = QuillVersion::try_from(version).unwrap_or_else(|e| error(e));
        if version != expected_version {
            error(format!(
                "component {} had version {}, but expected version {}, try updating again later",
                display_name, version, expected_version
            ));
        }
    }

    progress_bar.finish_with_message(format!("{} done", display_name));
}

async fn download_self(host: HostType, expected_version: QuillVersion) {
    let temp_dir = tokio::task::spawn_blocking(|| tempdir::TempDir::new("quill_install").unwrap())
        .await
        .unwrap();

    // Download quill itself and perform a self update.
    download_tar_gz_or_exit(
        format!(
            "https://github.com/quill-lang/quill/releases/download/latest-release/{}_quill.tar.gz",
            host.component_prefix()
        ),
        "quill",
        temp_dir.path().to_owned(),
        Some(expected_version),
    )
    .await;

    let self_path = std::env::current_exe().unwrap();
    let temp_path = self_path.with_extension("old");
    let _ = tokio::fs::remove_file(&temp_path).await;
    tokio::task::spawn_blocking(move || {
        self_update::Move::from_source(&host.as_executable(temp_dir.path().join("quill")))
            .replace_using_temp(&temp_path)
            .to_dest(&self_path)
            .unwrap();
    })
    .await
    .unwrap();
}

/// If unpack_inner_folder is true, the artifact contains exactly one folder with the same name, which will be unpacked.
async fn download_artifact(
    name: &str,
    display_name: &str,
    expected_version: Option<QuillVersion>,
    location: PathBuf,
    unpack_inner_folder: bool,
) {
    let temp_dir = tokio::task::spawn_blocking(|| tempdir::TempDir::new("quill_install").unwrap())
        .await
        .unwrap();

    // Download quill itself and perform a self update.
    download_tar_gz_or_exit(
        format!(
            "https://github.com/quill-lang/quill/releases/download/latest-release/{}.tar.gz",
            name
        ),
        display_name,
        temp_dir.path().to_owned(),
        expected_version,
    )
    .await;

    // Now that we know the unpacking was successful, copy the files from the temp dir into a known install dir.
    if unpack_inner_folder {
        let _ = tokio::fs::remove_dir_all(location.join(name)).await;
        let temp_path = temp_dir.into_path();
        tokio::fs::rename(temp_path.join(name), location.join(name))
            .await
            .unwrap();
        tokio::fs::remove_dir_all(temp_path).await.unwrap();
    } else {
        let _ = tokio::fs::remove_dir_all(&location).await;
        tokio::fs::rename(temp_dir.into_path(), location)
            .await
            .unwrap();
    }
}
