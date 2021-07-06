use std::{fmt::Display, path::PathBuf};

use flate2::bufread::GzDecoder;
use indicatif::{ProgressBar, ProgressStyle};
use tar::Archive;

static APP_USER_AGENT: &str = concat!(env!("CARGO_PKG_NAME"), "/", env!("CARGO_PKG_VERSION"),);

fn error<S: Display>(message: S) -> ! {
    println!("{} {}", console::style("error:").red().bright(), message);
    std::process::exit(1);
}

fn main() {
    let temp_dir = tempdir::TempDir::new("quill_install").unwrap();

    let file = format!(
        "https://github.com/quill-lang/quill/releases/download/latest/{}_quill.tar.gz",
        if cfg!(windows) {
            "windows-latest"
        } else {
            "ubuntu-latest"
        }
    );

    download_tar_gz_or_exit(&file, temp_dir.path().to_owned());

    let exe = temp_dir
        .path()
        .join(if cfg!(windows) { "quill.exe" } else { "quill" });

    let install_location = dirs::home_dir().unwrap().join(".quill");
    std::fs::create_dir_all(&install_location).unwrap();
    let new_exe = if let Some(ext) = exe.extension() {
        install_location.join("quill").with_extension(ext)
    } else {
        install_location.join("quill")
    };

    let _ = std::fs::remove_file(&new_exe);
    std::fs::rename(exe, &new_exe).unwrap();

    let status = std::process::Command::new(new_exe)
        .arg("update")
        .status()
        .unwrap();

    if status.success() {
        println!(
            "{}",
            console::style("Quill installed successfully!")
                .green()
                .bright()
                .bold()
        );
        println!(
            "To complete installation, add {} to your PATH.",
            console::style(install_location.to_string_lossy())
                .cyan()
                .bold()
        );
    }

    // Wait for user to press enter.
    std::io::stdin().read_line(&mut String::new()).unwrap();
}

fn download_tar_gz_or_exit(url: &str, dir: PathBuf) {
    let progress_bar = ProgressBar::new(1);
    progress_bar.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:30.cyan/blue}] {bytes}/{total_bytes} ({eta}) {msg}")
        .progress_chars("#>-")
    );
    progress_bar.set_message("connecting");
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
            progress_bar.set_message("downloading");
            progress_bar.set_length(std::cmp::max(total_bytes as u64, bytes_so_far as u64));
            progress_bar.set_position(bytes_so_far as u64);
        }
        true
    })
    .unwrap();

    if let Err(err) = xfer.perform() {
        error(format!("could not download (CURL error {})", err,))
    };

    drop(xfer);

    progress_bar.set_message("unpacking");

    let mut archive = Archive::new(GzDecoder::new(bytes.as_slice()));
    archive.unpack(dir).unwrap();

    progress_bar.finish_with_message("done");
}
