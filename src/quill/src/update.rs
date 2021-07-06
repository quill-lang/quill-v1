use std::{
    convert::{TryFrom, TryInto},
    fmt::Display,
    io::Cursor,
    path::PathBuf,
};

use chrono::{DateTime, FixedOffset};
use clap::ArgMatches;
use flate2::bufread::GzDecoder;
use indicatif::{ProgressBar, ProgressStyle};
use tar::Archive;
use xz2::read::XzDecoder;
use zip::ZipArchive;

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

#[derive(serde::Deserialize)]
struct ZigDownloadInfo {
    master: ZigReleaseDownloadInfo,
}
#[derive(serde::Deserialize)]
struct ZigReleaseDownloadInfo {
    // version: String,
    #[serde(rename = "x86_64-linux")]
    x86_64_linux: ZigRelease,
    #[serde(rename = "x86_64-windows")]
    x86_64_windows: ZigRelease,
}
#[derive(serde::Deserialize)]
struct ZigRelease {
    tarball: String,
    // shasum: String,
}

pub fn process_update(cli_config: &CliConfig, _args: &ArgMatches<'_>) {
    if let crate::CompilerLocation::Installed { host, root } = &cli_config.compiler_location {
        let _ = std::fs::remove_dir_all(root.join("compiler-deps"));
        let _ = std::fs::create_dir_all(root.join("compiler-deps"));

        eprintln!("checking latest version...",);
        let version: QuillVersion = download_text_or_exit(
            "https://github.com/quill-lang/quill/releases/download/latest/version.txt",
            "quill version",
        )
        .try_into()
        .unwrap_or_else(|e| error(e));
        eprintln!("installing quill {}", version);

        let exe_path = if let HostType::Windows = host {
            root.join("quill.exe")
        } else {
            root.join("quill")
        };
        download_self(*host, version, exe_path);

        // Download components such as quillc.
        std::fs::create_dir_all(root.join("compiler-deps")).unwrap();
        for component in &["quillc", "quill_lsp"] {
            download_artifact(
                &format!("{}_{}", host.component_prefix(), component),
                component,
                Some(version),
                root.join(component),
                false,
            );
        }

        // Download development components.
        std::fs::create_dir_all(root.join("compiler-deps")).unwrap();
        // Download the Zig compiler.
        let zig_version: ZigDownloadInfo = serde_json::from_str(&download_text_or_exit(
            "https://ziglang.org/download/index.json",
            "zig version",
        ))
        .unwrap_or_else(|e| error(e));
        let zig_release = zig_version.master;
        let zig_download = match host {
            HostType::Linux => zig_release.x86_64_linux,
            HostType::Windows => zig_release.x86_64_windows,
        };
        // Download the tarball.
        download_archive_or_exit(
            &zig_download.tarball,
            "zig compiler",
            root.join("compiler-deps").join("zig"),
            None,
        );
    } else {
        error("cannot update quill when running from source")
    }
}

fn download_text_or_exit(url: &str, request_name: &str) -> String {
    let mut bytes = Vec::new();
    let mut request = curl::easy::Easy::new();
    request.useragent(APP_USER_AGENT).unwrap();
    request.url(url).unwrap();
    request.follow_location(true).unwrap();
    let mut xfer = request.transfer();
    xfer.write_function(|data| {
        bytes.extend(data);
        Ok(data.len())
    })
    .unwrap();

    if let Err(err) = xfer.perform() {
        error(format!(
            "could not fetch {} (CURL error {})",
            request_name, err,
        ))
    } else {
        drop(xfer);
        match String::from_utf8(bytes) {
            Ok(string) => string,
            Err(err) => error(format!(
                "could not fetch {} (server returned an invalid string: {})",
                request_name, err,
            )),
        }
    }
}

/// If a version is provided, this function assumes that the tarball contains a `version.txt` file, and that the version should match the given expected version.
/// Archive types `tar.gz`, `tar.xz` and `zip` are supported.
/// If `zip` is provided, we assume that we're downloading the zig compiler, and special-case logic is used to remove the top-level
/// folder from the archive.
fn download_archive_or_exit(
    url: &str,
    display_name: &str,
    dir: PathBuf,
    expected_version: Option<QuillVersion>,
) {
    enum ArchiveType {
        TarGz,
        TarXz,
        Zip,
    }

    let archive_type = if url.ends_with("tar.gz") {
        ArchiveType::TarGz
    } else if url.ends_with("tar.xz") {
        ArchiveType::TarXz
    } else if url.ends_with("zip") {
        ArchiveType::Zip
    } else {
        panic!("url was {}", url)
    };

    let progress_bar = ProgressBar::new(1);
    progress_bar.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:30.cyan/blue}] {bytes}/{total_bytes} ({eta}) {msg}")
        .progress_chars("#>-")
    );
    progress_bar.set_message(format!("{} connecting", display_name));
    progress_bar.enable_steady_tick(50);

    let mut bytes = Vec::new();

    let mut request = curl::easy::Easy::new();
    request.useragent(APP_USER_AGENT).unwrap();
    request.url(url).unwrap();
    request.follow_location(true).unwrap();
    request.progress(true).unwrap();
    let mut xfer = request.transfer();
    xfer.write_function(|data| {
        bytes.extend(data);
        Ok(data.len())
    })
    .unwrap();
    xfer.progress_function(|total_bytes, bytes_so_far, _, _| {
        // If the total is zero, then we haven't finished parsing the HTTP header yet,
        // so we don't know how many bytes there are to download. So in this case,
        // we simply don't update the progress bar.
        if total_bytes as u64 != 0 {
            progress_bar.set_message(format!("{} downloading", display_name));
            progress_bar.set_length(std::cmp::max(total_bytes as u64, bytes_so_far as u64));
            progress_bar.set_position(bytes_so_far as u64);
        }
        true
    })
    .unwrap();

    if let Err(err) = xfer.perform() {
        error(format!(
            "could not download {} (CURL error {})",
            display_name, err,
        ))
    };

    drop(xfer);

    progress_bar.set_message(format!("{} unpacking", display_name));

    match archive_type {
        ArchiveType::TarGz => {
            let mut archive = Archive::new(GzDecoder::new(bytes.as_slice()));
            archive.unpack(&dir).unwrap();
        }
        ArchiveType::TarXz => {
            let mut archive = Archive::new(XzDecoder::new(bytes.as_slice()));
            archive.unpack(&dir).unwrap();
        }
        ArchiveType::Zip => {
            let mut archive = ZipArchive::new(Cursor::new(bytes)).unwrap();
            // Find the root folder of this archive.
            let prefix = {
                let mut path = archive
                    .by_index(0)
                    .unwrap()
                    .enclosed_name()
                    .unwrap()
                    .to_owned();
                while let Some(parent) = path.parent() {
                    if parent.file_name().is_some() {
                        path = parent.to_owned();
                    } else {
                        break;
                    }
                }
                path
            };
            for i in 0..archive.len() {
                let mut file = archive.by_index(i).unwrap();
                let outpath = match file.enclosed_name() {
                    Some(path) => dir.join(path.strip_prefix(&prefix).unwrap()),
                    None => continue,
                };

                if (&*file.name()).ends_with('/') {
                    std::fs::create_dir_all(&outpath).unwrap();
                } else {
                    if let Some(p) = outpath.parent() {
                        if !p.exists() {
                            std::fs::create_dir_all(&p).unwrap();
                        }
                    }
                    let mut outfile = std::fs::File::create(&outpath).unwrap();
                    std::io::copy(&mut file, &mut outfile).unwrap();
                }
            }
        }
    }

    // Check the version.
    if let Some(expected_version) = expected_version {
        let version = std::fs::read_to_string(dir.join("version.txt")).unwrap();
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

fn download_self(host: HostType, expected_version: QuillVersion, exe_path: PathBuf) {
    let temp_dir = tempdir::TempDir::new("quill_install").unwrap();

    // Download quill itself and perform a self update.
    download_archive_or_exit(
        &format!(
            "https://github.com/quill-lang/quill/releases/download/latest/{}_quill.tar.gz",
            host.component_prefix()
        ),
        "quill",
        temp_dir.path().to_owned(),
        Some(expected_version),
    );

    let temp_path = exe_path.with_extension("old");
    let _ = std::fs::remove_file(&temp_path);

    self_update::Move::from_source(&host.as_executable(temp_dir.path().join("quill")))
        .replace_using_temp(&temp_path)
        .to_dest(&exe_path)
        .unwrap();
}

/// If unpack_inner_folder is true, the artifact contains exactly one folder with the same name, which will be unpacked.
fn download_artifact(
    name: &str,
    display_name: &str,
    expected_version: Option<QuillVersion>,
    location: PathBuf,
    unpack_inner_folder: bool,
) {
    let temp_dir = tempdir::TempDir::new("quill_install").unwrap();

    // Download quill itself and perform a self update.
    download_archive_or_exit(
        &format!(
            "https://github.com/quill-lang/quill/releases/download/latest/{}.tar.gz",
            name
        ),
        display_name,
        temp_dir.path().to_owned(),
        expected_version,
    );

    // Now that we know the unpacking was successful, copy the files from the temp dir into a known install dir.
    if unpack_inner_folder {
        let _ = std::fs::remove_dir_all(location.join(name));
        let temp_path = temp_dir.into_path();
        std::fs::rename(temp_path.join(name), location.join(name)).unwrap();
        std::fs::remove_dir_all(temp_path).unwrap();
    } else {
        let _ = std::fs::remove_dir_all(&location);
        std::fs::rename(temp_dir.into_path(), location).unwrap();
    }
}
