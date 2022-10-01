//! A readonly filesystem that is backed by a raw radix tree.
//!
//! Values are files, paths are filenames, '/' is directory separator
use anyhow::Context;
use fuser::{
    FileAttr, FileType, Filesystem, ReplyAttr, ReplyData, ReplyDirectory, ReplyEntry, Request,
};
use libc::ENOENT;
use radixdb::store::{Blob, PagedFileStore};
use radixdb::{radixtree, RadixTree};
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::time::{Duration, UNIX_EPOCH};

const TTL: Duration = Duration::from_secs(1); // 1 second

fn mk_dir_attr(inode: u64) -> FileAttr {
    FileAttr {
        ino: inode,
        size: 0,
        blocks: 1,
        atime: UNIX_EPOCH, // 1970-01-01 00:00:00
        mtime: UNIX_EPOCH,
        ctime: UNIX_EPOCH,
        crtime: UNIX_EPOCH,
        kind: FileType::Directory,
        perm: 0o755,
        nlink: 2,
        uid: 501,
        gid: 20,
        rdev: 0,
        flags: 0,
        blksize: 4096,
    }
}

fn mk_file_attr(inode: u64, size: usize) -> FileAttr {
    let block_size: u32 = 4096;
    let mut blocks = (size / (block_size as usize)) as u64;
    if size % (block_size as usize) != 0 {
        blocks += 1;
    }
    FileAttr {
        ino: inode,
        size: size as u64,
        blocks,
        atime: UNIX_EPOCH, // 1970-01-01 00:00:00
        mtime: UNIX_EPOCH,
        ctime: UNIX_EPOCH,
        crtime: UNIX_EPOCH,
        kind: FileType::RegularFile,
        perm: 0o644,
        nlink: 1,
        uid: 501,
        gid: 20,
        rdev: 0,
        flags: 0,
        blksize: block_size,
    }
}

struct Directory {
    inode: u64,
    tree: RadixTree<PagedFileStore>,
    entries: Option<BTreeMap<String, u64>>,
}

struct File {
    inode: u64,
    content: Blob<'static>,
}

enum DEntry {
    File(File),
    Directory(Directory),
}

pub struct RawRadixFs {
    inodes: Vec<DEntry>,
}

impl RawRadixFs {
    pub fn open(file: std::fs::File) -> anyhow::Result<Self> {
        let store = PagedFileStore::new(file, 1024 * 1024)?;
        let id = store.last_id();
        let data = RadixTree::try_load(store, id.as_ref())?;
        Self::new(data)
    }

    pub fn new(tree: RadixTree<PagedFileStore>) -> anyhow::Result<Self> {
        let inodes = vec![DEntry::Directory(Directory {
            inode: 1,
            tree,
            entries: None,
        })];
        Ok(Self { inodes })
    }

    fn get_dentry(&self, inode: u64) -> anyhow::Result<&DEntry> {
        self.inodes.get(inode as usize - 1).context("no such inode")
    }

    fn get_dir(&self, inode: u64) -> anyhow::Result<&Directory> {
        if let DEntry::Directory(dir) = self.get_dentry(inode)? {
            Ok(dir)
        } else {
            Err(anyhow::anyhow!("not a directory"))
        }
    }

    fn get_file(&self, inode: u64) -> anyhow::Result<&File> {
        if let DEntry::File(file) = self.get_dentry(inode)? {
            Ok(file)
        } else {
            Err(anyhow::anyhow!("not a file"))
        }
    }

    fn get_dentry_mut(&mut self, inode: u64) -> anyhow::Result<&mut DEntry> {
        self.inodes
            .get_mut(inode as usize - 1)
            .context("no such inode")
    }

    fn get_dir_mut(&mut self, inode: u64) -> anyhow::Result<&mut Directory> {
        if let DEntry::Directory(dir) = self.get_dentry_mut(inode)? {
            Ok(dir)
        } else {
            Err(anyhow::anyhow!("not a directory"))
        }
    }

    /// lazily populate the entries of a directory
    fn init_entries(&mut self, inode: u64) -> anyhow::Result<()> {
        println!("init_entries {}", inode);
        let dir = self.get_dir(inode)?;
        // lazy load entries
        if dir.entries.is_none() {
            let mut entries = Vec::new();
            let mut by_name = BTreeMap::new();
            let mut next_inode = self.inodes.len() as u64 + 1;
            for item in dir.tree.try_group_by(|key, _| Ok(!key.contains(&b'/'))) {
                let tree = item?;
                println!("{:?}", tree);
                let prefix = tree.prefix().to_owned().load(RadixTree::store(&tree))?;
                // only add utf8 keys
                let key = match std::str::from_utf8(&prefix) {
                    Ok(key) => key,
                    Err(_) => continue,
                };
                if let Some(file) = tree.value() {
                    let inode = next_inode;
                    let content = file.to_owned().load(RadixTree::store(&dir.tree))?;
                    let entry = DEntry::File(File { inode, content });
                    entries.push(entry);
                    by_name.insert(key.to_string(), inode);
                    next_inode += 1;
                } else {
                    let offset = key.find('/').unwrap();
                    let dir_name = &key[..offset];
                    let tree = dir.tree.try_filter_prefix(&key[..=offset], &[])?;
                    let inode = next_inode;
                    let entry = DEntry::Directory(Directory {
                        inode,
                        tree,
                        entries: None,
                    });
                    entries.push(entry);
                    by_name.insert(dir_name.to_string(), inode);
                    next_inode += 1;
                }
            }
            self.inodes.extend(entries);
            self.get_dir_mut(inode)?.entries = Some(by_name);
        };
        Ok(())
    }

    /// lazily populate the entries of a directory
    fn get_dir_entries(&self, inode: u64) -> anyhow::Result<&BTreeMap<String, u64>> {
        self.get_dir(inode)?.entries.as_ref().context("no entries")
    }
}

impl Filesystem for RawRadixFs {
    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        println!("lookup {} {:?}", parent, name);
        if self.get_dir(parent).is_ok() {
            self.init_entries(parent).unwrap();
            let dir = self.get_dir_entries(parent).unwrap();
            println!("found dir {:?}", dir);
            if let Some(inode) = dir.get(name.to_str().unwrap()) {
                match self.get_dentry(*inode).unwrap() {
                    DEntry::File(file) => {
                        let attr = mk_file_attr(file.inode, file.content.as_ref().len());
                        reply.entry(&TTL, &attr, 0);
                    }
                    DEntry::Directory(dir) => {
                        let attr = mk_dir_attr(dir.inode);
                        reply.entry(&TTL, &attr, 0);
                    }
                }
            } else {
                reply.error(ENOENT);
            }
        } else {
            reply.error(ENOENT);
        }
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        println!("getattr {}", ino);
        if let Ok(dentry) = self.get_dentry(ino) {
            match dentry {
                DEntry::File(file) => {
                    reply.attr(&TTL, &mk_file_attr(file.inode, file.content.len()));
                }
                DEntry::Directory(dir) => {
                    reply.attr(&TTL, &mk_dir_attr(dir.inode));
                }
            }
        } else {
            reply.error(ENOENT);
        }
    }

    fn read(
        &mut self,
        _req: &Request,
        inode: u64,
        _fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock: Option<u64>,
        reply: ReplyData,
    ) {
        println!("read {} {} {}", inode, offset, size);
        match self.get_file(inode) {
            Ok(file) => {
                let content = &file.content;
                if offset >= content.len() as i64 {
                    reply.error(libc::ENOENT);
                    return;
                }
                let start = offset as usize;
                let end = usize::min(start + size as usize, content.len());
                let data = &content[start..end];
                reply.data(data);
            }
            Err(_) => reply.error(ENOENT),
        }
    }

    fn readdir(
        &mut self,
        _req: &Request,
        inode: u64,
        _fh: u64,
        offset: i64,
        mut reply: ReplyDirectory,
    ) {
        println!("readdir {} {}", inode, offset);
        self.init_entries(inode).unwrap();
        let entries = self.get_dir_entries(inode).unwrap();
        // default entries
        let dir_entries = vec![
            (inode, FileType::Directory, "."),
            (inode, FileType::Directory, ".."),
        ]
        .into_iter();
        let entries = entries.iter().map(|(name, inode)| {
            let entry = self.get_dentry(*inode).unwrap();
            let file_type = match entry {
                DEntry::Directory(_) => FileType::Directory,
                DEntry::File(_) => FileType::RegularFile,
            };
            (*inode, file_type, name.as_str())
        });
        let res = dir_entries.chain(entries).skip(offset as usize);
        for (i, (inode, file_type, name)) in res.enumerate() {
            // i + 1 means the index of the next entry
            if reply.add(inode, (i + 1) as i64, file_type, name) {
                break;
            }
        }
        reply.ok();
    }
}

pub fn mk_example_tree() -> RadixTree {
    radixtree! {
        "usr/bin/joe" => "joe",
        "usr/bin/emacs" => "emacs",
        "usr/bin/vim" => "vim",
        "usr/bin/gedit" => "gedit",
        "usr/lib/libc.so" => "libc",
        "usr/lib/libm.so" => "libm",
        "etc/passwd" => "root:x:0:0:root:/root:/bin/bash",
        "etc/group" => "root:x:0:",
    }
}
