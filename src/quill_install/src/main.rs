use std::{fmt::Display, path::PathBuf, sync::atomic::Ordering};

use flate2::bufread::GzDecoder;
use indicatif::{ProgressBar, ProgressStyle};
use reqwest::IntoUrl;
use tar::Archive;

static APP_USER_AGENT: &str = concat!(env!("CARGO_PKG_NAME"), "/", env!("CARGO_PKG_VERSION"),);

fn error<S: Display>(message: S) -> ! {
    println!("{} {}", console::style("error:").red().bright(), message);
    std::process::exit(1);
}

#[tokio::main]
async fn main() {
    let temp_dir = tokio::task::spawn_blocking(|| tempdir::TempDir::new("quill_install").unwrap())
        .await
        .unwrap();

    let file = format!(
        "https://github.com/quill-lang/quill/releases/download/latest/{}_quill.tar.gz",
        if cfg!(windows) {
            "windows-latest"
        } else {
            "ubuntu-latest"
        }
    );

    download_tar_gz_or_exit(file, temp_dir.path().to_owned()).await;

    let exe = temp_dir
        .path()
        .join(if cfg!(windows) { "quill.exe" } else { "quill" });

    let install_location = dirs::home_dir().unwrap().join(".quill");
    tokio::fs::create_dir_all(&install_location).await.unwrap();
    let new_exe = if let Some(ext) = exe.extension() {
        install_location.join("quill").with_extension(ext)
    } else {
        install_location.join("quill")
    };

    let _ = tokio::fs::remove_file(&new_exe).await;
    tokio::fs::rename(exe, &new_exe).await.unwrap();

    let status = tokio::process::Command::new(new_exe)
        .arg("update")
        .status()
        .await
        .unwrap();

    if status.success() {
        println!(
            "{}",
            console::style("Quill installed successfully!")
                .green()
                .bright()
                .bold()
        );
    }
}

async fn download_tar_gz_or_exit<U: IntoUrl>(url: U, dir: PathBuf) {
    let mut response = match reqwest::Client::builder()
        .user_agent(APP_USER_AGENT)
        .build()
        .unwrap()
        .get(url)
        .send()
        .await
    {
        Ok(response) => response,
        Err(_) => error("could not download quill (could not connect to server)"),
    };

    if !response.status().is_success() {
        error(format!(
            "could not download quill (connected but server returned error code '{}')",
            response.status()
        ))
    }

    let length = response.content_length().unwrap();
    let progress_bar = ProgressBar::new(length);
    progress_bar.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:30.cyan/blue}] {bytes}/{total_bytes} ({eta}) {msg}")
        .progress_chars("#>-")
    );
    progress_bar.set_message("downloading");

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
            Err(_) => {
                error("could not download quill (connected but could not retrieve response body)")
            }
        }
    }

    progress_bar.set_message("unpacking");
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

    progress_bar.finish_with_message("done");
}
