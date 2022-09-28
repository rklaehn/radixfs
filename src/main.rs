#![allow(clippy::needless_return)]

use clap::{crate_version, Arg, Command};
use fuser::TimeOrNow::Now;
use fuser::{
    Filesystem, KernelConfig, MountOption, ReplyAttr, ReplyCreate, ReplyData, ReplyDirectory,
    ReplyEmpty, ReplyEntry, ReplyOpen, ReplyStatfs, ReplyWrite, ReplyXattr, Request, TimeOrNow,
    FUSE_ROOT_ID,
};
use log::{debug, info, warn};
use log::{error, LevelFilter};
use parking_lot::Mutex;
use radixdb::RadixTree;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::io::{Cursor, ErrorKind};
use std::ops::Range;
use std::os::raw::c_int;
use std::os::unix::ffi::OsStrExt;
#[cfg(target_os = "linux")]
use std::os::unix::io::IntoRawFd;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

const BLOCK_SIZE: u64 = 512;
const MAX_NAME_LENGTH: u32 = 255;
const MAX_FILE_SIZE: u64 = 1024 * 1024 * 1024 * 1024;

// Top two file handle bits are used to store permissions
// Note: This isn't safe, since the client can modify those bits. However, this implementation
// is just a toy
const FILE_HANDLE_READ_BIT: u64 = 1 << 63;
const FILE_HANDLE_WRITE_BIT: u64 = 1 << 62;

const FMODE_EXEC: i32 = 0x20;

type Inode = u64;

type DirectoryDescriptor = BTreeMap<Vec<u8>, (Inode, FileKind)>;

#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq)]
enum FileKind {
    File,
    Directory,
    Symlink,
}

impl From<FileKind> for fuser::FileType {
    fn from(kind: FileKind) -> Self {
        match kind {
            FileKind::File => fuser::FileType::RegularFile,
            FileKind::Directory => fuser::FileType::Directory,
            FileKind::Symlink => fuser::FileType::Symlink,
        }
    }
}

#[derive(Debug)]
enum XattrNamespace {
    Security,
    System,
    Trusted,
    User,
}

fn parse_xattr_namespace(key: &[u8]) -> Result<XattrNamespace, c_int> {
    let user = b"user.";
    if key.len() < user.len() {
        return Err(libc::ENOTSUP);
    }
    if key[..user.len()].eq(user) {
        return Ok(XattrNamespace::User);
    }

    let system = b"system.";
    if key.len() < system.len() {
        return Err(libc::ENOTSUP);
    }
    if key[..system.len()].eq(system) {
        return Ok(XattrNamespace::System);
    }

    let trusted = b"trusted.";
    if key.len() < trusted.len() {
        return Err(libc::ENOTSUP);
    }
    if key[..trusted.len()].eq(trusted) {
        return Ok(XattrNamespace::Trusted);
    }

    let security = b"security";
    if key.len() < security.len() {
        return Err(libc::ENOTSUP);
    }
    if key[..security.len()].eq(security) {
        return Ok(XattrNamespace::Security);
    }

    return Err(libc::ENOTSUP);
}

fn clear_suid_sgid(attr: &mut InodeAttributes) {
    attr.mode &= !libc::S_ISUID as u16;
    // SGID is only suppose to be cleared if XGRP is set
    if attr.mode & libc::S_IXGRP as u16 != 0 {
        attr.mode &= !libc::S_ISGID as u16;
    }
}

fn creation_gid(parent: &InodeAttributes, gid: u32) -> u32 {
    if parent.mode & libc::S_ISGID as u16 != 0 {
        return parent.gid;
    }

    gid
}

fn xattr_access_check(
    key: &[u8],
    access_mask: i32,
    inode_attrs: &InodeAttributes,
    request: &Request<'_>,
) -> Result<(), c_int> {
    match parse_xattr_namespace(key)? {
        XattrNamespace::Security => {
            if access_mask != libc::R_OK && request.uid() != 0 {
                return Err(libc::EPERM);
            }
        }
        XattrNamespace::Trusted => {
            if request.uid() != 0 {
                return Err(libc::EPERM);
            }
        }
        XattrNamespace::System => {
            if key.eq(b"system.posix_acl_access") {
                if !check_access(
                    inode_attrs.uid,
                    inode_attrs.gid,
                    inode_attrs.mode,
                    request.uid(),
                    request.gid(),
                    access_mask,
                ) {
                    return Err(libc::EPERM);
                }
            } else if request.uid() != 0 {
                return Err(libc::EPERM);
            }
        }
        XattrNamespace::User => {
            if !check_access(
                inode_attrs.uid,
                inode_attrs.gid,
                inode_attrs.mode,
                request.uid(),
                request.gid(),
                access_mask,
            ) {
                return Err(libc::EPERM);
            }
        }
    }

    Ok(())
}

fn time_now() -> (i64, u32) {
    time_from_system_time(&SystemTime::now())
}

fn system_time_from_time(secs: i64, nsecs: u32) -> SystemTime {
    if secs >= 0 {
        UNIX_EPOCH + Duration::new(secs as u64, nsecs)
    } else {
        UNIX_EPOCH - Duration::new((-secs) as u64, nsecs)
    }
}

fn time_from_system_time(system_time: &SystemTime) -> (i64, u32) {
    // Convert to signed 64-bit time with epoch at 0
    match system_time.duration_since(UNIX_EPOCH) {
        Ok(duration) => (duration.as_secs() as i64, duration.subsec_nanos()),
        Err(before_epoch_error) => (
            -(before_epoch_error.duration().as_secs() as i64),
            before_epoch_error.duration().subsec_nanos(),
        ),
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct InodeAttributes {
    pub inode: Inode,
    pub open_file_handles: u64, // Ref count of open file handles to this inode
    pub size: u64,
    pub last_accessed: (i64, u32),
    pub last_modified: (i64, u32),
    pub last_metadata_changed: (i64, u32),
    pub kind: FileKind,
    // Permissions and special mode bits
    pub mode: u16,
    pub hardlinks: u32,
    pub uid: u32,
    pub gid: u32,
    pub xattrs: BTreeMap<Vec<u8>, Vec<u8>>,
}

impl From<InodeAttributes> for fuser::FileAttr {
    fn from(attrs: InodeAttributes) -> Self {
        fuser::FileAttr {
            ino: attrs.inode,
            size: attrs.size,
            blocks: (attrs.size + BLOCK_SIZE - 1) / BLOCK_SIZE,
            atime: system_time_from_time(attrs.last_accessed.0, attrs.last_accessed.1),
            mtime: system_time_from_time(attrs.last_modified.0, attrs.last_modified.1),
            ctime: system_time_from_time(
                attrs.last_metadata_changed.0,
                attrs.last_metadata_changed.1,
            ),
            crtime: SystemTime::UNIX_EPOCH,
            kind: attrs.kind.into(),
            perm: attrs.mode,
            nlink: attrs.hardlinks,
            uid: attrs.uid,
            gid: attrs.gid,
            rdev: 0,
            blksize: BLOCK_SIZE as u32,
            flags: 0,
        }
    }
}

// Stores inode metadata data in "$data_dir/inodes" and file contents in "$data_dir/contents"
// Directory data is stored in the file's contents, as a serialized DirectoryDescriptor
struct RadixFS {
    inner: Arc<Mutex<Inner>>,
}

impl RadixFS {
    fn new() -> RadixFS {
        RadixFS {
            inner: Default::default(),
        }
    }
}

const fn inode_prefix() -> [u8; 4] {
    *b"inod"
}

fn inode_key(inode: Inode) -> [u8; 12] {
    let mut res = [0u8; 12];
    res[0..4].copy_from_slice(&inode_prefix());
    res[4..].copy_from_slice(&inode.to_be_bytes());
    res
}

fn content_prefix(inode: Inode) -> [u8; 12] {
    let mut res = [0u8; 12];
    res[0..4].copy_from_slice(b"data");
    res[4..12].copy_from_slice(&inode.to_be_bytes());
    res
}

fn content_key(inode: Inode, page: u64) -> [u8; 20] {
    let mut res = [0u8; 20];
    res[0..4].copy_from_slice(b"data");
    res[4..12].copy_from_slice(&inode.to_be_bytes());
    res[12..20].copy_from_slice(&page.to_be_bytes());
    res
}

type PartialPage = Option<(u64, Range<usize>)>;

/// Given a range of offsets and a page size, calculate which pages fully cover the range.
///
/// Returns a triple of (optional first partial page, optional range of full pages, optional last partial page)
fn pages_from_range(
    range: Range<u64>,
    block_size: usize,
) -> (PartialPage, Range<u64>, PartialPage) {
    let start = range.start;
    let end = range.end;
    let block_size_u64 = block_size as u64;
    let start_offset = (start % block_size_u64) as usize;
    let start_page = start / block_size_u64;
    let start_page_full = start_offset == 0;
    if range.is_empty() {
        // Special case: empty range
        return (Some((start_page, start_offset..start_offset)), 0..0, None);
    }
    let end_page = (end - 1) / block_size_u64;
    let end_offset = (end % block_size_u64) as usize;
    let end_page_full = end_offset == 0;
    let (first, mut range, last) = if start_page_full && end_page_full {
        // just full pages
        (None, start_page..end_page + 1, None)
    } else if start_page == end_page {
        // just one partial page
        (Some((start_page, start_offset..end_offset)), 0..0, None)
    } else if start_page_full {
        // start page full, end page partial
        (None, start_page..end_page, Some((end_page, 0..end_offset)))
    } else if end_page_full {
        // start page partial, end page full
        (
            Some((start_page, start_offset..block_size)),
            start_page + 1..end_page + 1,
            None,
        )
    } else {
        // start page partial, end page partial
        (
            Some((start_page, start_offset..block_size)),
            start_page + 1..end_page,
            Some((end_page, 0..end_offset)),
        )
    };
    if range.is_empty() {
        range = 0..0;
    }
    (first, range, last)
}

#[test]
fn test_pages_from_range() {
    assert_eq!(pages_from_range(0..0, 10), (Some((0, 0..0)), 0..0, None));
    assert_eq!(pages_from_range(0..1, 10), (Some((0, 0..1)), 0..0, None));
    assert_eq!(pages_from_range(10..11, 10), (Some((1, 0..1)), 0..0, None));
    assert_eq!(pages_from_range(0..10, 10), (None, 0..1, None));
    assert_eq!(pages_from_range(0..20, 10), (None, 0..2, None));
    assert_eq!(
        pages_from_range(1..19, 10),
        (Some((0, 1..10)), 0..0, Some((1, 0..9)))
    );
    assert_eq!(pages_from_range(0..30, 10), (None, 0..3, None));
    assert_eq!(pages_from_range(0..29, 10), (None, 0..2, Some((2, 0..9))));
    assert_eq!(pages_from_range(1..30, 10), (Some((0, 1..10)), 1..3, None));
}

#[derive(Debug, Default, Clone)]
struct Inner {
    next_file_handle: u64,
    data: RadixTree,
}

impl Inner {
    fn read_page(&self, inode: Inode, page: u64, buf: &mut [u8]) -> usize {
        println!("read_page {} {} {}", inode, page, buf.len());
        if let Some(page) = self.data.get(content_key(inode, page)) {
            let len = buf.len().min(page.len());
            buf[..len].copy_from_slice(&page[..len]);
            len
        } else {
            0
        }
    }

    fn write_page(&mut self, inode: Inode, page: u64, data: &[u8]) {
        println!("write_page {} {} {}", inode, page, data.len());
        self.data.insert(content_key(inode, page), data);
    }

    fn read_all(&self, inode: Inode) -> Option<Vec<u8>> {
        let mut res = None;
        for (_, value) in self.data.scan_prefix(content_prefix(inode)) {
            res.get_or_insert(Vec::new())
                .extend_from_slice(value.as_ref());
        }
        debug!("read_all {} {:?}", inode, res);
        res
    }

    fn write_range(&mut self, inode: Inode, offset: u64, data: &[u8]) {
        let write_range = offset..offset + (u64::try_from(data.len()).unwrap());
        let (first, full, last) = pages_from_range(write_range, 4096);
        let mut t = [0u8; 4096];
        let mut d = data;
        // write first incomplete page
        if let Some((page, range)) = first {
            let len = self.read_page(inode, page, &mut t);
            let (curr, rest) = d.split_at(range.len());
            t[range.clone()].copy_from_slice(curr);
            self.write_page(inode, page, &t[..len.max(range.end)]);
            d = rest;
        }
        // write full pages
        if !full.is_empty() {
            for page in full {
                let (curr, rest) = d.split_at(4096);
                t.copy_from_slice(curr);
                self.write_page(inode, page, &t);
                d = rest;
            }
        }
        // write last incomplete page
        if let Some((page, range)) = last {
            let len = self.read_page(inode, page, &mut t);
            let (curr, rest) = d.split_at(range.len());
            t[range.clone()].copy_from_slice(curr);
            self.write_page(inode, page, &t[..len.max(range.end)]);
            d = rest;
        }
        assert!(d.is_empty());
    }

    fn write_all(&mut self, inode: Inode, data: &[u8]) {
        self.data.remove_prefix(content_prefix(inode));
        self.write_range(inode, 0, data);
    }

    fn creation_mode(&self, mode: u32) -> u16 {
        (mode & !(libc::S_ISUID | libc::S_ISGID) as u32) as u16
    }

    fn allocate_next_inode(&self) -> Inode {
        let inodes = self.data.filter_prefix(inode_prefix());
        let current_inode = if let Some((k, _)) = inodes.last_entry(vec![]) {
            u64::from_be_bytes(k[4..].try_into().unwrap())
        } else {
            fuser::FUSE_ROOT_ID
        };
        info!("allocate_next_inode {}", current_inode + 1);
        current_inode + 1
    }

    fn allocate_next_file_handle(&mut self, read: bool, write: bool) -> u64 {
        self.next_file_handle += 1;
        let mut fh = self.next_file_handle;
        // Assert that we haven't run out of file handles
        assert!(fh < FILE_HANDLE_WRITE_BIT && fh < FILE_HANDLE_READ_BIT);
        if read {
            fh |= FILE_HANDLE_READ_BIT;
        }
        if write {
            fh |= FILE_HANDLE_WRITE_BIT;
        }

        fh
    }

    fn check_file_handle_read(&self, file_handle: u64) -> bool {
        (file_handle & FILE_HANDLE_READ_BIT) != 0
    }

    fn check_file_handle_write(&self, file_handle: u64) -> bool {
        (file_handle & FILE_HANDLE_WRITE_BIT) != 0
    }

    fn get_directory_content(&self, inode: Inode) -> Result<DirectoryDescriptor, c_int> {
        if let Some(data) = self.read_all(inode) {
            Ok(bincode::deserialize_from(Cursor::new(data)).unwrap())
        } else {
            Err(libc::ENOENT)
        }
    }

    fn write_directory_content(&mut self, inode: Inode, entries: DirectoryDescriptor) {
        let data = bincode::serialize(&entries).unwrap();
        self.write_all(inode, &data);
    }

    fn get_inode(&self, inode: Inode) -> Result<InodeAttributes, c_int> {
        info!("get_inode({})", inode);
        if let Some(value) = self.data.get(&inode_key(inode)) {
            let attrs: InodeAttributes = bincode::deserialize(value.as_ref()).unwrap();
            Ok(attrs)
        } else {
            Err(libc::ENOENT)
        }
    }

    fn write_inode(&mut self, inode: &InodeAttributes) {
        info!("write_inode({:?})", inode);
        let bytes = bincode::serialize(inode).unwrap();
        self.data.insert(inode_key(inode.inode), bytes);
    }

    // Check whether a file should be removed from storage. Should be called after decrementing
    // the link count, or closing a file handle
    fn gc_inode(&mut self, inode: &InodeAttributes) -> bool {
        if inode.hardlinks == 0 && inode.open_file_handles == 0 {
            self.data.remove(inode_key(inode.inode));
            self.data.remove_prefix(content_prefix(inode.inode));

            return true;
        }

        return false;
    }

    fn file_len(&self, inode: Inode) -> Option<u64> {
        let tree = self.data.filter_prefix(content_prefix(inode));
        if let Some((k, v)) = tree.last_entry(vec![]) {
            let page_offset = u64::from_be_bytes(k[12..].try_into().unwrap());
            let page_len = v.len() as u64;
            Some(page_offset + page_len)
        } else {
            None
        }
    }

    fn truncate(
        &mut self,
        inode: Inode,
        new_length: u64,
        uid: u32,
        gid: u32,
    ) -> Result<InodeAttributes, c_int> {
        if new_length > MAX_FILE_SIZE {
            return Err(libc::EFBIG);
        }

        let mut attrs = self.get_inode(inode)?;

        if !check_access(attrs.uid, attrs.gid, attrs.mode, uid, gid, libc::W_OK) {
            return Err(libc::EACCES);
        }

        if let Some(len) = self.file_len(inode) {
            #[allow(clippy::comparison_chain)]
            if len > new_length {
                let (first, full, last) = pages_from_range(new_length..len, 4096);
                // truncate the first page
                if let Some((first_page, range)) = first {
                    let mut buf = [0u8; 4096];
                    let len = self.read_page(inode, first_page, &mut buf);
                    self.write_page(inode, first_page, &buf[..range.start.min(len)]);
                }
                // remove all full pages
                for page in full {
                    self.data.remove(content_key(inode, page));
                }
                // remove partial last page
                if let Some((last_page, _)) = last {
                    self.data.remove(content_key(inode, last_page));
                }
            } else if len < new_length {
                let t = vec![0u8; (new_length - len) as usize];
                self.write_range(inode, len, &t);
            } else {
                // nothing to do
            }
        }

        let now = time_now();
        attrs.size = new_length;
        attrs.last_metadata_changed = now;
        attrs.last_modified = now;

        // Clear SETUID & SETGID on truncate
        clear_suid_sgid(&mut attrs);

        self.write_inode(&attrs);

        Ok(attrs)
    }

    fn lookup_name(&self, parent: u64, name: &OsStr) -> Result<InodeAttributes, c_int> {
        let entries = self.get_directory_content(parent)?;
        if let Some((inode, _)) = entries.get(name.as_bytes()) {
            return self.get_inode(*inode);
        } else {
            return Err(libc::ENOENT);
        }
    }

    fn insert_link(
        &mut self,
        req: &Request,
        parent: u64,
        name: &OsStr,
        inode: u64,
        kind: FileKind,
    ) -> Result<(), c_int> {
        if self.lookup_name(parent, name).is_ok() {
            return Err(libc::EEXIST);
        }

        let mut parent_attrs = self.get_inode(parent)?;

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            return Err(libc::EACCES);
        }
        let now = time_now();
        parent_attrs.last_modified = now;
        parent_attrs.last_metadata_changed = now;
        self.write_inode(&parent_attrs);

        let mut entries = self.get_directory_content(parent).unwrap();
        entries.insert(name.as_bytes().to_vec(), (inode, kind));
        self.write_directory_content(parent, entries);

        Ok(())
    }
}

impl Filesystem for RadixFS {
    fn init(
        &mut self,
        _req: &Request,
        #[allow(unused_variables)] config: &mut KernelConfig,
    ) -> Result<(), c_int> {
        let mut inner = self.inner.lock();
        let now = time_now();
        if inner.get_inode(FUSE_ROOT_ID).is_err() {
            // Initialize with empty filesystem
            let root = InodeAttributes {
                inode: FUSE_ROOT_ID,
                open_file_handles: 0,
                size: 0,
                last_accessed: now,
                last_modified: now,
                last_metadata_changed: now,
                kind: FileKind::Directory,
                mode: 0o777,
                hardlinks: 2,
                uid: 0,
                gid: 0,
                xattrs: Default::default(),
            };
            inner.write_inode(&root);
            let mut entries = BTreeMap::new();
            entries.insert(b".".to_vec(), (FUSE_ROOT_ID, FileKind::Directory));
            inner.write_directory_content(FUSE_ROOT_ID, entries);
        }
        Ok(())
    }

    fn lookup(&mut self, req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        if name.len() > MAX_NAME_LENGTH as usize {
            reply.error(libc::ENAMETOOLONG);
            return;
        }
        let inner = self.inner.lock();
        let parent_attrs = inner.get_inode(parent).unwrap();
        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::X_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }

        match inner.lookup_name(parent, name) {
            Ok(attrs) => reply.entry(&Duration::new(0, 0), &attrs.into(), 0),
            Err(error_code) => reply.error(error_code),
        }
    }

    fn forget(&mut self, _req: &Request, _ino: u64, _nlookup: u64) {}

    fn getattr(&mut self, _req: &Request, inode: u64, reply: ReplyAttr) {
        let inner = self.inner.lock();
        match inner.get_inode(inode) {
            Ok(attrs) => reply.attr(&Duration::new(0, 0), &attrs.into()),
            Err(error_code) => reply.error(error_code),
        }
    }

    fn setattr(
        &mut self,
        req: &Request,
        inode: u64,
        mode: Option<u32>,
        uid: Option<u32>,
        gid: Option<u32>,
        size: Option<u64>,
        atime: Option<TimeOrNow>,
        mtime: Option<TimeOrNow>,
        _ctime: Option<SystemTime>,
        fh: Option<u64>,
        _crtime: Option<SystemTime>,
        _chgtime: Option<SystemTime>,
        _bkuptime: Option<SystemTime>,
        _flags: Option<u32>,
        reply: ReplyAttr,
    ) {
        let mut inner = self.inner.lock();
        let mut attrs = match inner.get_inode(inode) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        let now = time_now();
        if let Some(mode) = mode {
            debug!("chmod() called with {:?}, {:o}", inode, mode);
            if req.uid() != 0 && req.uid() != attrs.uid {
                reply.error(libc::EPERM);
                return;
            }
            if req.uid() != 0
                && req.gid() != attrs.gid
                && !get_groups(req.pid()).contains(&attrs.gid)
            {
                // If SGID is set and the file belongs to a group that the caller is not part of
                // then the SGID bit is suppose to be cleared during chmod
                attrs.mode = (mode & !libc::S_ISGID as u32) as u16;
            } else {
                attrs.mode = mode as u16;
            }
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
            reply.attr(&Duration::new(0, 0), &attrs.into());
            return;
        }

        if uid.is_some() || gid.is_some() {
            debug!("chown() called with {:?} {:?} {:?}", inode, uid, gid);
            if let Some(gid) = gid {
                // Non-root users can only change gid to a group they're in
                if req.uid() != 0 && !get_groups(req.pid()).contains(&gid) {
                    reply.error(libc::EPERM);
                    return;
                }
            }
            if let Some(uid) = uid {
                if req.uid() != 0
                    // but no-op changes by the owner are not an error
                    && !(uid == attrs.uid && req.uid() == attrs.uid)
                {
                    reply.error(libc::EPERM);
                    return;
                }
            }
            // Only owner may change the group
            if gid.is_some() && req.uid() != 0 && req.uid() != attrs.uid {
                reply.error(libc::EPERM);
                return;
            }

            if attrs.mode & (libc::S_IXUSR | libc::S_IXGRP | libc::S_IXOTH) as u16 != 0 {
                // SUID & SGID are suppose to be cleared when chown'ing an executable file
                clear_suid_sgid(&mut attrs);
            }

            if let Some(uid) = uid {
                attrs.uid = uid;
                // Clear SETUID on owner change
                attrs.mode &= !libc::S_ISUID as u16;
            }
            if let Some(gid) = gid {
                attrs.gid = gid;
                // Clear SETGID unless user is root
                if req.uid() != 0 {
                    attrs.mode &= !libc::S_ISGID as u16;
                }
            }
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
            reply.attr(&Duration::new(0, 0), &attrs.into());
            return;
        }

        if let Some(size) = size {
            debug!("truncate() called with {:?} {:?}", inode, size);
            if let Some(handle) = fh {
                // If the file handle is available, check access locally.
                // This is important as it preserves the semantic that a file handle opened
                // with W_OK will never fail to truncate, even if the file has been subsequently
                // chmod'ed
                if inner.check_file_handle_write(handle) {
                    if let Err(error_code) = inner.truncate(inode, size, 0, 0) {
                        reply.error(error_code);
                        return;
                    }
                } else {
                    reply.error(libc::EACCES);
                    return;
                }
            } else if let Err(error_code) = inner.truncate(inode, size, req.uid(), req.gid()) {
                reply.error(error_code);
                return;
            }
        }

        let now = time_now();
        if let Some(atime) = atime {
            debug!("utimens() called with {:?}, atime={:?}", inode, atime);

            if attrs.uid != req.uid() && req.uid() != 0 && atime != Now {
                reply.error(libc::EPERM);
                return;
            }

            if attrs.uid != req.uid()
                && !check_access(
                    attrs.uid,
                    attrs.gid,
                    attrs.mode,
                    req.uid(),
                    req.gid(),
                    libc::W_OK,
                )
            {
                reply.error(libc::EACCES);
                return;
            }

            attrs.last_accessed = match atime {
                TimeOrNow::SpecificTime(time) => time_from_system_time(&time),
                Now => now,
            };
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
        }
        if let Some(mtime) = mtime {
            debug!("utimens() called with {:?}, mtime={:?}", inode, mtime);

            if attrs.uid != req.uid() && req.uid() != 0 && mtime != Now {
                reply.error(libc::EPERM);
                return;
            }

            if attrs.uid != req.uid()
                && !check_access(
                    attrs.uid,
                    attrs.gid,
                    attrs.mode,
                    req.uid(),
                    req.gid(),
                    libc::W_OK,
                )
            {
                reply.error(libc::EACCES);
                return;
            }

            attrs.last_modified = match mtime {
                TimeOrNow::SpecificTime(time) => time_from_system_time(&time),
                Now => now,
            };
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
        }

        let attrs = inner.get_inode(inode).unwrap();
        reply.attr(&Duration::new(0, 0), &attrs.into());
        return;
    }

    fn readlink(&mut self, _req: &Request, inode: u64, reply: ReplyData) {
        debug!("readlink() called on {:?}", inode);
        let inner = self.inner.lock();
        if let Some(file) = inner.data.get(content_key(inode, 0)) {
            reply.data(file.as_ref());
        } else {
            reply.error(libc::ENOENT);
        }
    }

    fn mknod(
        &mut self,
        req: &Request,
        parent: u64,
        name: &OsStr,
        mut mode: u32,
        _umask: u32,
        _rdev: u32,
        reply: ReplyEntry,
    ) {
        let file_type = mode & libc::S_IFMT as u32;

        if file_type != libc::S_IFREG as u32
            && file_type != libc::S_IFLNK as u32
            && file_type != libc::S_IFDIR as u32
        {
            // TODO
            warn!("mknod() implementation is incomplete. Only supports regular files, symlinks, and directories. Got {:o}", mode);
            reply.error(libc::ENOSYS);
            return;
        }

        let mut inner = self.inner.lock();
        if inner.lookup_name(parent, name).is_ok() {
            reply.error(libc::EEXIST);
            return;
        }

        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }
        let now = time_now();
        parent_attrs.last_modified = now;
        parent_attrs.last_metadata_changed = now;
        inner.write_inode(&parent_attrs);

        if req.uid() != 0 {
            mode &= !(libc::S_ISUID | libc::S_ISGID) as u32;
        }

        let inode = inner.allocate_next_inode();
        let attrs = InodeAttributes {
            inode,
            open_file_handles: 0,
            size: 0,
            last_accessed: now,
            last_modified: now,
            last_metadata_changed: now,
            kind: as_file_kind(mode),
            mode: inner.creation_mode(mode),
            hardlinks: 1,
            uid: req.uid(),
            gid: creation_gid(&parent_attrs, req.gid()),
            xattrs: Default::default(),
        };
        inner.write_inode(&attrs);
        inner.write_all(inode, &[]);

        if as_file_kind(mode) == FileKind::Directory {
            let mut entries = BTreeMap::new();
            entries.insert(b".".to_vec(), (inode, FileKind::Directory));
            entries.insert(b"..".to_vec(), (parent, FileKind::Directory));
            inner.write_directory_content(inode, entries);
        }

        let mut entries = inner.get_directory_content(parent).unwrap();
        entries.insert(name.as_bytes().to_vec(), (inode, attrs.kind));
        inner.write_directory_content(parent, entries);

        // TODO: implement flags
        reply.entry(&Duration::new(0, 0), &attrs.into(), 0);
    }

    fn mkdir(
        &mut self,
        req: &Request,
        parent: u64,
        name: &OsStr,
        mut mode: u32,
        _umask: u32,
        reply: ReplyEntry,
    ) {
        debug!("mkdir() called with {:?} {:?} {:o}", parent, name, mode);
        let mut inner = self.inner.lock();
        if inner.lookup_name(parent, name).is_ok() {
            reply.error(libc::EEXIST);
            return;
        }

        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }
        let now = time_now();
        parent_attrs.last_modified = now;
        parent_attrs.last_metadata_changed = now;
        inner.write_inode(&parent_attrs);

        if req.uid() != 0 {
            mode &= !(libc::S_ISUID | libc::S_ISGID) as u32;
        }
        if parent_attrs.mode & libc::S_ISGID as u16 != 0 {
            mode |= libc::S_ISGID as u32;
        }

        let inode = inner.allocate_next_inode();
        let attrs = InodeAttributes {
            inode,
            open_file_handles: 0,
            size: BLOCK_SIZE,
            last_accessed: now,
            last_modified: now,
            last_metadata_changed: now,
            kind: FileKind::Directory,
            mode: inner.creation_mode(mode),
            hardlinks: 2, // Directories start with link count of 2, since they have a self link
            uid: req.uid(),
            gid: creation_gid(&parent_attrs, req.gid()),
            xattrs: Default::default(),
        };
        inner.write_inode(&attrs);

        let mut entries = BTreeMap::new();
        entries.insert(b".".to_vec(), (inode, FileKind::Directory));
        entries.insert(b"..".to_vec(), (parent, FileKind::Directory));
        inner.write_directory_content(inode, entries);

        let mut entries = inner.get_directory_content(parent).unwrap();
        entries.insert(name.as_bytes().to_vec(), (inode, FileKind::Directory));
        inner.write_directory_content(parent, entries);

        reply.entry(&Duration::new(0, 0), &attrs.into(), 0);
    }

    fn unlink(&mut self, req: &Request, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        debug!("unlink() called with {:?} {:?}", parent, name);
        let mut inner = self.inner.lock();
        let mut attrs = match inner.lookup_name(parent, name) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }

        let uid = req.uid();
        // "Sticky bit" handling
        if parent_attrs.mode & libc::S_ISVTX as u16 != 0
            && uid != 0
            && uid != parent_attrs.uid
            && uid != attrs.uid
        {
            reply.error(libc::EACCES);
            return;
        }

        let now = time_now();
        parent_attrs.last_metadata_changed = now;
        parent_attrs.last_modified = now;
        inner.write_inode(&parent_attrs);

        attrs.hardlinks -= 1;
        attrs.last_metadata_changed = now;
        inner.write_inode(&attrs);
        inner.gc_inode(&attrs);

        let mut entries = inner.get_directory_content(parent).unwrap();
        entries.remove(name.as_bytes());
        inner.write_directory_content(parent, entries);

        reply.ok();
    }

    fn rmdir(&mut self, req: &Request, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        debug!("rmdir() called with {:?} {:?}", parent, name);
        let mut inner = self.inner.lock();
        let mut attrs = match inner.lookup_name(parent, name) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        // Directories always have a self and parent link
        if inner.get_directory_content(attrs.inode).unwrap().len() > 2 {
            reply.error(libc::ENOTEMPTY);
            return;
        }
        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }

        // "Sticky bit" handling
        if parent_attrs.mode & libc::S_ISVTX as u16 != 0
            && req.uid() != 0
            && req.uid() != parent_attrs.uid
            && req.uid() != attrs.uid
        {
            reply.error(libc::EACCES);
            return;
        }

        let now = time_now();
        parent_attrs.last_metadata_changed = now;
        parent_attrs.last_modified = now;
        inner.write_inode(&parent_attrs);

        attrs.hardlinks = 0;
        attrs.last_metadata_changed = now;
        inner.write_inode(&attrs);
        inner.gc_inode(&attrs);

        let mut entries = inner.get_directory_content(parent).unwrap();
        entries.remove(name.as_bytes());
        inner.write_directory_content(parent, entries);

        reply.ok();
    }

    fn symlink(
        &mut self,
        req: &Request,
        parent: u64,
        name: &OsStr,
        link: &Path,
        reply: ReplyEntry,
    ) {
        debug!("symlink() called with {:?} {:?} {:?}", parent, name, link);
        let mut inner = self.inner.lock();
        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }
        let now = time_now();
        parent_attrs.last_modified = now;
        parent_attrs.last_metadata_changed = now;
        inner.write_inode(&parent_attrs);

        let inode = inner.allocate_next_inode();
        let attrs = InodeAttributes {
            inode,
            open_file_handles: 0,
            size: link.as_os_str().as_bytes().len() as u64,
            last_accessed: now,
            last_modified: now,
            last_metadata_changed: now,
            kind: FileKind::Symlink,
            mode: 0o777,
            hardlinks: 1,
            uid: req.uid(),
            gid: creation_gid(&parent_attrs, req.gid()),
            xattrs: Default::default(),
        };

        if let Err(error_code) = inner.insert_link(req, parent, name, inode, FileKind::Symlink) {
            reply.error(error_code);
            return;
        }
        inner.write_inode(&attrs);
        inner.write_all(inode, link.as_os_str().as_bytes());
        reply.entry(&Duration::new(0, 0), &attrs.into(), 0);
    }

    fn rename(
        &mut self,
        req: &Request,
        parent: u64,
        name: &OsStr,
        new_parent: u64,
        new_name: &OsStr,
        _flags: u32,
        reply: ReplyEmpty,
    ) {
        let mut inner = self.inner.lock();
        let mut inode_attrs = match inner.lookup_name(parent, name) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }

        // "Sticky bit" handling
        if parent_attrs.mode & libc::S_ISVTX as u16 != 0
            && req.uid() != 0
            && req.uid() != parent_attrs.uid
            && req.uid() != inode_attrs.uid
        {
            reply.error(libc::EACCES);
            return;
        }

        let mut new_parent_attrs = match inner.get_inode(new_parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            new_parent_attrs.uid,
            new_parent_attrs.gid,
            new_parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }

        // "Sticky bit" handling in new_parent
        if new_parent_attrs.mode & libc::S_ISVTX as u16 != 0 {
            if let Ok(existing_attrs) = inner.lookup_name(new_parent, new_name) {
                if req.uid() != 0
                    && req.uid() != new_parent_attrs.uid
                    && req.uid() != existing_attrs.uid
                {
                    reply.error(libc::EACCES);
                    return;
                }
            }
        }

        let now = time_now();
        #[cfg(target_os = "linux")]
        if flags & libc::RENAME_EXCHANGE as u32 != 0 {
            let mut new_inode_attrs = match self.lookup_name(new_parent, new_name) {
                Ok(attrs) => attrs,
                Err(error_code) => {
                    reply.error(error_code);
                    return;
                }
            };

            let mut entries = self.get_directory_content(new_parent).unwrap();
            entries.insert(
                new_name.as_bytes().to_vec(),
                (inode_attrs.inode, inode_attrs.kind),
            );
            self.write_directory_content(new_parent, entries);

            let mut entries = self.get_directory_content(parent).unwrap();
            entries.insert(
                name.as_bytes().to_vec(),
                (new_inode_attrs.inode, new_inode_attrs.kind),
            );
            self.write_directory_content(parent, entries);

            parent_attrs.last_metadata_changed = now;
            parent_attrs.last_modified = now;
            self.write_inode(&parent_attrs);
            new_parent_attrs.last_metadata_changed = now;
            new_parent_attrs.last_modified = now;
            self.write_inode(&new_parent_attrs);
            inode_attrs.last_metadata_changed = now;
            self.write_inode(&inode_attrs);
            new_inode_attrs.last_metadata_changed = now;
            self.write_inode(&new_inode_attrs);

            if inode_attrs.kind == FileKind::Directory {
                let mut entries = self.get_directory_content(inode_attrs.inode).unwrap();
                entries.insert(b"..".to_vec(), (new_parent, FileKind::Directory));
                self.write_directory_content(inode_attrs.inode, entries);
            }
            if new_inode_attrs.kind == FileKind::Directory {
                let mut entries = self.get_directory_content(new_inode_attrs.inode).unwrap();
                entries.insert(b"..".to_vec(), (parent, FileKind::Directory));
                self.write_directory_content(new_inode_attrs.inode, entries);
            }

            reply.ok();
            return;
        }

        // Only overwrite an existing directory if it's empty
        if let Ok(new_name_attrs) = inner.lookup_name(new_parent, new_name) {
            if new_name_attrs.kind == FileKind::Directory
                && inner
                    .get_directory_content(new_name_attrs.inode)
                    .unwrap()
                    .len()
                    > 2
            {
                reply.error(libc::ENOTEMPTY);
                return;
            }
        }

        // Only move an existing directory to a new parent, if we have write access to it,
        // because that will change the ".." link in it
        if inode_attrs.kind == FileKind::Directory
            && parent != new_parent
            && !check_access(
                inode_attrs.uid,
                inode_attrs.gid,
                inode_attrs.mode,
                req.uid(),
                req.gid(),
                libc::W_OK,
            )
        {
            reply.error(libc::EACCES);
            return;
        }

        // If target already exists decrement its hardlink count
        if let Ok(mut existing_inode_attrs) = inner.lookup_name(new_parent, new_name) {
            let mut entries = inner.get_directory_content(new_parent).unwrap();
            entries.remove(new_name.as_bytes());
            inner.write_directory_content(new_parent, entries);

            if existing_inode_attrs.kind == FileKind::Directory {
                existing_inode_attrs.hardlinks = 0;
            } else {
                existing_inode_attrs.hardlinks -= 1;
            }
            existing_inode_attrs.last_metadata_changed = now;
            inner.write_inode(&existing_inode_attrs);
            inner.gc_inode(&existing_inode_attrs);
        }

        let mut entries = inner.get_directory_content(parent).unwrap();
        entries.remove(name.as_bytes());
        inner.write_directory_content(parent, entries);

        let mut entries = inner.get_directory_content(new_parent).unwrap();
        entries.insert(
            new_name.as_bytes().to_vec(),
            (inode_attrs.inode, inode_attrs.kind),
        );
        inner.write_directory_content(new_parent, entries);

        parent_attrs.last_metadata_changed = now;
        parent_attrs.last_modified = now;
        inner.write_inode(&parent_attrs);
        new_parent_attrs.last_metadata_changed = now;
        new_parent_attrs.last_modified = now;
        inner.write_inode(&new_parent_attrs);
        inode_attrs.last_metadata_changed = now;
        inner.write_inode(&inode_attrs);

        if inode_attrs.kind == FileKind::Directory {
            let mut entries = inner.get_directory_content(inode_attrs.inode).unwrap();
            entries.insert(b"..".to_vec(), (new_parent, FileKind::Directory));
            inner.write_directory_content(inode_attrs.inode, entries);
        }

        reply.ok();
    }

    fn link(
        &mut self,
        req: &Request,
        inode: u64,
        new_parent: u64,
        new_name: &OsStr,
        reply: ReplyEntry,
    ) {
        debug!(
            "link() called for {}, {}, {:?}",
            inode, new_parent, new_name
        );
        let mut inner = self.inner.lock();
        let mut attrs = match inner.get_inode(inode) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };
        let now = time_now();
        if let Err(error_code) = inner.insert_link(req, new_parent, new_name, inode, attrs.kind) {
            reply.error(error_code);
        } else {
            attrs.hardlinks += 1;
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
            reply.entry(&Duration::new(0, 0), &attrs.into(), 0);
        }
    }

    fn open(&mut self, req: &Request, inode: u64, flags: i32, reply: ReplyOpen) {
        debug!("open() called for {:?}", inode);
        let mut inner = self.inner.lock();
        let (access_mask, read, write) = match flags & libc::O_ACCMODE {
            libc::O_RDONLY => {
                // Behavior is undefined, but most filesystems return EACCES
                if flags & libc::O_TRUNC != 0 {
                    reply.error(libc::EACCES);
                    return;
                }
                if flags & FMODE_EXEC != 0 {
                    // Open is from internal exec syscall
                    (libc::X_OK, true, false)
                } else {
                    (libc::R_OK, true, false)
                }
            }
            libc::O_WRONLY => (libc::W_OK, false, true),
            libc::O_RDWR => (libc::R_OK | libc::W_OK, true, true),
            // Exactly one access mode flag must be specified
            _ => {
                reply.error(libc::EINVAL);
                return;
            }
        };

        match inner.get_inode(inode) {
            Ok(mut attr) => {
                if check_access(
                    attr.uid,
                    attr.gid,
                    attr.mode,
                    req.uid(),
                    req.gid(),
                    access_mask,
                ) {
                    attr.open_file_handles += 1;
                    inner.write_inode(&attr);
                    let open_flags = 0;
                    reply.opened(inner.allocate_next_file_handle(read, write), open_flags);
                } else {
                    reply.error(libc::EACCES);
                }
                return;
            }
            Err(error_code) => reply.error(error_code),
        }
    }

    fn read(
        &mut self,
        _req: &Request,
        inode: u64,
        fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyData,
    ) {
        println!(
            "read() called on {:?} offset={:?} size={:?}",
            inode, offset, size
        );
        assert!(offset >= 0);
        let inner = self.inner.lock();
        if !inner.check_file_handle_read(fh) {
            reply.error(libc::EACCES);
            return;
        }

        if !inner.data.has_prefix(content_prefix(inode)) {
            reply.error(libc::ENOENT);
            return;
        }

        let range = offset as u64..offset as u64 + size as u64;
        let (first, full, last) = pages_from_range(range, 4096);
        let mut t = [0u8; 4096];
        let mut res = Vec::<u8>::with_capacity(size as usize);
        if let Some((page, range)) = first {
            let _ = inner.read_page(inode, page, &mut t);
            res.extend_from_slice(&t[range]);
        }
        if !full.is_empty() {
            for page in full {
                let _ = inner.read_page(inode, page, &mut t);
                res.extend_from_slice(&t);
            }
        }
        if let Some((page, range)) = last {
            let _ = inner.read_page(inode, page, &mut t);
            res.extend_from_slice(&t[range]);
        }
        reply.data(&res);
    }

    fn write(
        &mut self,
        _req: &Request,
        inode: u64,
        fh: u64,
        offset: i64,
        data: &[u8],
        _write_flags: u32,
        #[allow(unused_variables)] flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyWrite,
    ) {
        println!(
            "write() called with {:?} offset={} size={:?}",
            inode,
            offset,
            data.len()
        );
        assert!(offset >= 0);
        let mut inner = self.inner.lock();
        if !inner.check_file_handle_write(fh) {
            reply.error(libc::EACCES);
            return;
        }

        if inner.data.has_prefix(content_prefix(inode)) {
            let now = time_now();
            inner.write_range(inode, offset.try_into().unwrap(), data);
            let mut attrs = inner.get_inode(inode).unwrap();
            attrs.last_metadata_changed = now;
            attrs.last_modified = now;
            if data.len() + offset as usize > attrs.size as usize {
                attrs.size = (data.len() + offset as usize) as u64;
            }
            clear_suid_sgid(&mut attrs);
            inner.write_inode(&attrs);

            reply.written(data.len() as u32);
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn release(
        &mut self,
        _req: &Request<'_>,
        inode: u64,
        _fh: u64,
        _flags: i32,
        _lock_owner: Option<u64>,
        _flush: bool,
        reply: ReplyEmpty,
    ) {
        let mut inner = self.inner.lock();
        if let Ok(mut attrs) = inner.get_inode(inode) {
            attrs.open_file_handles -= 1;
            inner.write_inode(&attrs);
        }
        reply.ok();
    }

    fn opendir(&mut self, req: &Request, inode: u64, flags: i32, reply: ReplyOpen) {
        info!("opendir() called on {:?}", inode);
        let (access_mask, read, write) = match flags & libc::O_ACCMODE {
            libc::O_RDONLY => {
                // Behavior is undefined, but most filesystems return EACCES
                if flags & libc::O_TRUNC != 0 {
                    reply.error(libc::EACCES);
                    return;
                }
                (libc::R_OK, true, false)
            }
            libc::O_WRONLY => (libc::W_OK, false, true),
            libc::O_RDWR => (libc::R_OK | libc::W_OK, true, true),
            // Exactly one access mode flag must be specified
            _ => {
                reply.error(libc::EINVAL);
                return;
            }
        };
        let mut inner = self.inner.lock();

        match inner.get_inode(inode) {
            Ok(mut attr) => {
                if check_access(
                    attr.uid,
                    attr.gid,
                    attr.mode,
                    req.uid(),
                    req.gid(),
                    access_mask,
                ) {
                    attr.open_file_handles += 1;
                    inner.write_inode(&attr);
                    let open_flags = 0;
                    reply.opened(inner.allocate_next_file_handle(read, write), open_flags);
                } else {
                    reply.error(libc::EACCES);
                }
                return;
            }
            Err(error_code) => reply.error(error_code),
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
        debug!("readdir() called with {:?}", inode);
        assert!(offset >= 0);
        let inner = self.inner.lock();
        let entries = match inner.get_directory_content(inode) {
            Ok(entries) => entries,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        for (index, entry) in entries.iter().skip(offset as usize).enumerate() {
            let (name, (inode, file_type)) = entry;

            let buffer_full: bool = reply.add(
                *inode,
                offset + index as i64 + 1,
                (*file_type).into(),
                OsStr::from_bytes(name),
            );

            if buffer_full {
                break;
            }
        }

        reply.ok();
    }

    fn releasedir(
        &mut self,
        _req: &Request<'_>,
        inode: u64,
        _fh: u64,
        _flags: i32,
        reply: ReplyEmpty,
    ) {
        info!("releasedir {}", inode);
        let mut inner = self.inner.lock();
        if let Ok(mut attrs) = inner.get_inode(inode) {
            attrs.open_file_handles -= 1;
            inner.write_inode(&attrs);
        }
        reply.ok();
    }

    fn statfs(&mut self, _req: &Request, _ino: u64, reply: ReplyStatfs) {
        info!("statfs() implementation is a stub");
        // TODO: real implementation of this
        reply.statfs(
            10_000,
            10_000,
            10_000,
            1,
            10_000,
            BLOCK_SIZE as u32,
            MAX_NAME_LENGTH,
            BLOCK_SIZE as u32,
        );
    }

    fn setxattr(
        &mut self,
        request: &Request<'_>,
        inode: u64,
        key: &OsStr,
        value: &[u8],
        _flags: i32,
        _position: u32,
        reply: ReplyEmpty,
    ) {
        let mut inner = self.inner.lock();
        if let Ok(mut attrs) = inner.get_inode(inode) {
            if let Err(error) = xattr_access_check(key.as_bytes(), libc::W_OK, &attrs, request) {
                reply.error(error);
                return;
            }

            let now = time_now();
            attrs.xattrs.insert(key.as_bytes().to_vec(), value.to_vec());
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
            reply.ok();
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn getxattr(
        &mut self,
        request: &Request<'_>,
        inode: u64,
        key: &OsStr,
        size: u32,
        reply: ReplyXattr,
    ) {
        let inner = self.inner.lock();
        if let Ok(attrs) = inner.get_inode(inode) {
            if let Err(error) = xattr_access_check(key.as_bytes(), libc::R_OK, &attrs, request) {
                reply.error(error);
                return;
            }

            if let Some(data) = attrs.xattrs.get(key.as_bytes()) {
                if size == 0 {
                    reply.size(data.len() as u32);
                } else if data.len() <= size as usize {
                    reply.data(data);
                } else {
                    reply.error(libc::ERANGE);
                }
            } else {
                #[cfg(target_os = "linux")]
                reply.error(libc::ENODATA);
                #[cfg(not(target_os = "linux"))]
                reply.error(libc::ENOATTR);
            }
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn listxattr(&mut self, _req: &Request<'_>, inode: u64, size: u32, reply: ReplyXattr) {
        let inner = self.inner.lock();
        if let Ok(attrs) = inner.get_inode(inode) {
            let mut bytes = vec![];
            // Convert to concatenated null-terminated strings
            for key in attrs.xattrs.keys() {
                bytes.extend(key);
                bytes.push(0);
            }
            if size == 0 {
                reply.size(bytes.len() as u32);
            } else if bytes.len() <= size as usize {
                reply.data(&bytes);
            } else {
                reply.error(libc::ERANGE);
            }
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn removexattr(&mut self, request: &Request<'_>, inode: u64, key: &OsStr, reply: ReplyEmpty) {
        let mut inner = self.inner.lock();
        if let Ok(mut attrs) = inner.get_inode(inode) {
            if let Err(error) = xattr_access_check(key.as_bytes(), libc::W_OK, &attrs, request) {
                reply.error(error);
                return;
            }

            let now = time_now();
            if attrs.xattrs.remove(key.as_bytes()).is_none() {
                #[cfg(target_os = "linux")]
                reply.error(libc::ENODATA);
                #[cfg(not(target_os = "linux"))]
                reply.error(libc::ENOATTR);
                return;
            }
            attrs.last_metadata_changed = now;
            inner.write_inode(&attrs);
            reply.ok();
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn access(&mut self, req: &Request, inode: u64, mask: i32, reply: ReplyEmpty) {
        debug!("access() called with {:?} {:?}", inode, mask);
        let inner = self.inner.lock();
        match inner.get_inode(inode) {
            Ok(attr) => {
                if check_access(attr.uid, attr.gid, attr.mode, req.uid(), req.gid(), mask) {
                    reply.ok();
                } else {
                    reply.error(libc::EACCES);
                }
            }
            Err(error_code) => reply.error(error_code),
        }
    }

    fn create(
        &mut self,
        req: &Request,
        parent: u64,
        name: &OsStr,
        mut mode: u32,
        _umask: u32,
        flags: i32,
        reply: ReplyCreate,
    ) {
        debug!("create() called with {:?} {:?}", parent, name);
        let mut inner = self.inner.lock();
        if inner.lookup_name(parent, name).is_ok() {
            reply.error(libc::EEXIST);
            return;
        }

        let (read, write) = match flags & libc::O_ACCMODE {
            libc::O_RDONLY => (true, false),
            libc::O_WRONLY => (false, true),
            libc::O_RDWR => (true, true),
            // Exactly one access mode flag must be specified
            _ => {
                reply.error(libc::EINVAL);
                return;
            }
        };

        let now = time_now();
        let mut parent_attrs = match inner.get_inode(parent) {
            Ok(attrs) => attrs,
            Err(error_code) => {
                reply.error(error_code);
                return;
            }
        };

        if !check_access(
            parent_attrs.uid,
            parent_attrs.gid,
            parent_attrs.mode,
            req.uid(),
            req.gid(),
            libc::W_OK,
        ) {
            reply.error(libc::EACCES);
            return;
        }
        parent_attrs.last_modified = now;
        parent_attrs.last_metadata_changed = now;
        inner.write_inode(&parent_attrs);

        if req.uid() != 0 {
            mode &= !(libc::S_ISUID | libc::S_ISGID) as u32;
        }

        let inode = inner.allocate_next_inode();
        let attrs = InodeAttributes {
            inode,
            open_file_handles: 1,
            size: 0,
            last_accessed: now,
            last_modified: now,
            last_metadata_changed: now,
            kind: as_file_kind(mode),
            mode: inner.creation_mode(mode),
            hardlinks: 1,
            uid: req.uid(),
            gid: creation_gid(&parent_attrs, req.gid()),
            xattrs: Default::default(),
        };
        inner.write_inode(&attrs);
        inner.write_all(inode, &[]);

        if as_file_kind(mode) == FileKind::Directory {
            let mut entries = BTreeMap::new();
            entries.insert(b".".to_vec(), (inode, FileKind::Directory));
            entries.insert(b"..".to_vec(), (parent, FileKind::Directory));
            inner.write_directory_content(inode, entries);
        }

        let mut entries = inner.get_directory_content(parent).unwrap();
        entries.insert(name.as_bytes().to_vec(), (inode, attrs.kind));
        inner.write_directory_content(parent, entries);

        // TODO: implement flags
        reply.created(
            &Duration::new(0, 0),
            &attrs.into(),
            0,
            inner.allocate_next_file_handle(read, write),
            0,
        );
    }

    #[cfg(target_os = "linux")]
    fn fallocate(
        &mut self,
        _req: &Request<'_>,
        inode: u64,
        _fh: u64,
        offset: i64,
        length: i64,
        mode: i32,
        reply: ReplyEmpty,
    ) {
        let path = self.content_path(inode);
        if let Ok(file) = OpenOptions::new().write(true).open(&path) {
            unsafe {
                libc::fallocate64(file.into_raw_fd(), mode, offset, length);
            }
            if mode & libc::FALLOC_FL_KEEP_SIZE == 0 {
                let mut attrs = self.get_inode(inode).unwrap();
                attrs.last_metadata_changed = now;
                attrs.last_modified = now;
                if (offset + length) as u64 > attrs.size {
                    attrs.size = (offset + length) as u64;
                }
                self.write_inode(&attrs);
            }
            reply.ok();
        } else {
            reply.error(libc::ENOENT);
        }
    }

    #[allow(unused_variables, unused_mut)]
    fn copy_file_range(
        &mut self,
        _req: &Request<'_>,
        src_inode: u64,
        src_fh: u64,
        src_offset: i64,
        dest_inode: u64,
        dest_fh: u64,
        dest_offset: i64,
        size: u64,
        _flags: u32,
        reply: ReplyWrite,
    ) {
        println!(
            "copy_file_range() called with src ({}, {}, {}) dest ({}, {}, {}) size={}",
            src_fh, src_inode, src_offset, dest_fh, dest_inode, dest_offset, size
        );
        let inner = self.inner.lock();
        if !inner.check_file_handle_read(src_fh) {
            reply.error(libc::EACCES);
            return;
        }
        if !inner.check_file_handle_write(dest_fh) {
            reply.error(libc::EACCES);
            return;
        }
        let now = time_now();
        let src_offset = usize::try_from(src_offset).unwrap();
        let dest_offset = usize::try_from(dest_offset).unwrap();
        let size = usize::try_from(size).unwrap();

        let mut inner = self.inner.lock();
        if inner.data.has_prefix(content_prefix(src_inode)) {
            // todo!();
            // let file_size = src_file.len();
            // // Could underflow if file length is less than local_start
            // let read_size = min(size, file_size.saturating_sub(src_offset));
            // let tmp = src_file[src_offset..src_offset + read_size].to_vec();

            // if let Some(dest_file) = inner.data.get_mut(&dest_inode) {
            //     dest_file[dest_offset..dest_offset + read_size].copy_from_slice(&tmp);

            //     let mut attrs = inner.get_inode(dest_inode).unwrap();
            //     attrs.last_metadata_changed = now;
            //     attrs.last_modified = now;
            //     if inner.data.len() + dest_offset as usize > attrs.size as usize {
            //         attrs.size = (inner.data.len() + dest_offset as usize) as u64;
            //     }
            //     inner.write_inode(&attrs);

            //     reply.written(inner.data.len() as u32);
            // } else {
            //     reply.error(libc::EBADF);
            // }
        } else {
            reply.error(libc::ENOENT);
        }
    }
}

pub fn check_access(
    file_uid: u32,
    file_gid: u32,
    file_mode: u16,
    uid: u32,
    gid: u32,
    mut access_mask: i32,
) -> bool {
    // F_OK tests for existence of file
    if access_mask == libc::F_OK {
        return true;
    }
    let file_mode = i32::from(file_mode);

    // root is allowed to read & write anything
    if uid == 0 {
        // root only allowed to exec if one of the X bits is set
        access_mask &= libc::X_OK;
        access_mask -= access_mask & (file_mode >> 6);
        access_mask -= access_mask & (file_mode >> 3);
        access_mask -= access_mask & file_mode;
        return access_mask == 0;
    }

    if uid == file_uid {
        access_mask -= access_mask & (file_mode >> 6);
    } else if gid == file_gid {
        access_mask -= access_mask & (file_mode >> 3);
    } else {
        access_mask -= access_mask & file_mode;
    }

    return access_mask == 0;
}

fn as_file_kind(mut mode: u32) -> FileKind {
    mode &= libc::S_IFMT as u32;

    if mode == libc::S_IFREG as u32 {
        return FileKind::File;
    } else if mode == libc::S_IFLNK as u32 {
        return FileKind::Symlink;
    } else if mode == libc::S_IFDIR as u32 {
        return FileKind::Directory;
    } else {
        unimplemented!("{}", mode);
    }
}

fn get_groups(_pid: u32) -> Vec<u32> {
    #[cfg(not(target_os = "macos"))]
    {
        let path = format!("/proc/{}/task/{}/status", pid, pid);
        let file = File::open(path).unwrap();
        for line in BufReader::new(file).lines() {
            let line = line.unwrap();
            if line.starts_with("Groups:") {
                return line["Groups: ".len()..]
                    .split(' ')
                    .filter(|x| !x.trim().is_empty())
                    .map(|x| x.parse::<u32>().unwrap())
                    .collect();
            }
        }
    }

    vec![]
}

fn main() {
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
    options.push(MountOption::AutoUnmount);

    let mountpoint: String = matches
        .value_of("mount-point")
        .unwrap_or_default()
        .to_string();

    let result = fuser::mount2(RadixFS::new(), mountpoint, &options);
    if let Err(e) = result {
        // Return a special error code for permission denied, which usually indicates that
        // "user_allow_other" is missing from /etc/fuse.conf
        if e.kind() == ErrorKind::PermissionDenied {
            error!("{}", e.to_string());
            std::process::exit(2);
        }
    }
}
