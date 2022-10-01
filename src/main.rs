#![allow(clippy::needless_return)]

use std::{fs::OpenOptions, io::ErrorKind};

use clap::{crate_version, Arg, Command};
use fuser::MountOption;
use log::LevelFilter;
mod raw_radix_fs;
use radixdb::store::PagedFileStore;
use raw_radix_fs::RawRadixFs;
mod rw_radix_fs;
use rw_radix_fs::RwRadixFs;

fn main() -> anyhow::Result<()> {
    let matches = Command::new("radixfs")
        .version(crate_version!())
        .author("Rüdiger Klaehn")
        .arg(
            Arg::new("mount-point")
                .long("mount-point")
                .value_name("MOUNT_POINT")
                .default_value("")
                .help("Act as a client, and mount FUSE at given path")
                .takes_value(true),
        )
        .arg(
            Arg::new("block-file")
                .long("block-file")
                .value_name("BLOCK_FILE")
                .help("Mount the given radixdb block file")
                .takes_value(true),
        )
        .arg(
            Arg::new("auto_unmount")
                .long("auto_unmount")
                .help("Automatically unmount on process exit"),
        )
        .arg(
            Arg::new("allow-root")
                .long("allow-root")
                .help("Allow root user to access filesystem"),
        )
        .arg(
            Arg::new("v")
                .short('v')
                .multiple_occurrences(true)
                .help("Sets the level of verbosity"),
        )
        .get_matches();

    let verbosity: u64 = matches.occurrences_of("v");
    let log_level = match verbosity {
        0 => LevelFilter::Error,
        1 => LevelFilter::Warn,
        2 => LevelFilter::Info,
        3 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };
    env_logger::builder()
        .format_timestamp_nanos()
        .filter_level(log_level)
        .init();

    let mut options = vec![MountOption::FSName("fuser".to_string())];
    if matches.is_present("auto_unmount") {
        options.push(MountOption::AutoUnmount);
    }
    if matches.is_present("allow-root") {
        options.push(MountOption::AllowRoot);
    }
    options.push(MountOption::AutoUnmount);

    let mountpoint: String = matches
        .value_of("mount-point")
        .unwrap_or_default()
        .to_string();

    let file_name: String = matches
        .value_of("block-file")
        .unwrap_or("radixfs.db")
        .to_string();

    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(file_name)?;
    let rw = false;
    if rw {
        let filesystem = RwRadixFs::open(file)?;
        let result = fuser::mount2(filesystem, mountpoint, &options);
        if let Err(e) = result {
            // Return a special error code for permission denied, which usually indicates that
            // "user_allow_other" is missing from /etc/fuse.conf
            if e.kind() == ErrorKind::PermissionDenied {
                log::error!("{}", e.to_string());
                std::process::exit(2);
            }
        }
    } else {
        let store = PagedFileStore::new(file, 1024 * 1024)?;
        let tree = raw_radix_fs::mk_example_tree().try_attached(store)?;
        let filesystem = RawRadixFs::new(tree)?;
        let result = fuser::mount2(filesystem, mountpoint, &options);
        if let Err(e) = result {
            // Return a special error code for permission denied, which usually indicates that
            // "user_allow_other" is missing from /etc/fuse.conf
            if e.kind() == ErrorKind::PermissionDenied {
                log::error!("{}", e.to_string());
                std::process::exit(2);
            }
        }
    }
    Ok(())
}
