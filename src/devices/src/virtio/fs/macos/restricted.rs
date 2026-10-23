use std::ffi::CStr;
use std::fs::File;
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, RwLock};
use std::time::Duration;

use super::confined::{Root, check_result, error, read_link};
use super::passthrough::{InodeAltKey, PermissionSemantics, fstat};
use crate::virtio::bindings;
use crate::virtio::fs::filesystem::{Context, Entry, FileSystem, FsOptions};
use crate::virtio::fs::fuse;
use crate::virtio::fs::inode_alloc::InodeAllocator;
use crate::virtio::fs::multikey::MultikeyBTreeMap;

struct InodeData {
    inode: u64,
    file: File,
    refcount: AtomicU64,
}

pub(super) struct RestrictedFs {
    root: Root,
    inodes: RwLock<MultikeyBTreeMap<u64, InodeAltKey, Arc<InodeData>>>,
    inode_alloc: Arc<InodeAllocator>,
}

impl RestrictedFs {
    pub(super) fn new(path: &Path, inode_alloc: Arc<InodeAllocator>) -> io::Result<Self> {
        Ok(Self {
            root: Root::new(path)?,
            inodes: RwLock::new(MultikeyBTreeMap::new()),
            inode_alloc,
        })
    }

    fn inode(&self, inode: u64) -> io::Result<Arc<InodeData>> {
        let data = self
            .inodes
            .read()
            .unwrap()
            .get(&inode)
            .cloned()
            .ok_or_else(|| error(libc::EBADF))?;
        self.root.check(&data.file)?;
        Ok(data)
    }

    fn entry(&self, ctx: Context, file: File) -> io::Result<Entry> {
        let st = self.root.check(&file)?;
        let key = InodeAltKey {
            ino: st.st_ino,
            dev: st.st_dev,
        };
        let mut inodes = self.inodes.write().unwrap();
        let data = if let Some(data) = inodes.get_alt(&key) {
            data.refcount.fetch_add(1, Ordering::Relaxed);
            data.clone()
        } else {
            let inode = self.inode_alloc.next();
            let data = Arc::new(InodeData {
                inode,
                file,
                refcount: AtomicU64::new(1),
            });
            inodes.insert(inode, key, data.clone());
            data
        };
        Ok(Entry {
            inode: data.inode,
            generation: 0,
            attr: fstat(
                &ctx,
                PermissionSemantics::LinuxSimplified,
                data.file.as_raw_fd(),
                false,
            )?,
            attr_flags: 0,
            attr_timeout: Duration::ZERO,
            entry_timeout: Duration::ZERO,
        })
    }
}

impl FileSystem for RestrictedFs {
    type Inode = u64;
    type Handle = u64;

    fn init(&self, _capable: FsOptions) -> io::Result<FsOptions> {
        let file = self.root.resolve(Path::new(""), false)?;
        let st = self.root.check(&file)?;
        self.inodes.write().unwrap().insert(
            fuse::ROOT_ID,
            InodeAltKey {
                ino: st.st_ino,
                dev: st.st_dev,
            },
            Arc::new(InodeData {
                inode: fuse::ROOT_ID,
                file,
                refcount: AtomicU64::new(2),
            }),
        );
        Ok(FsOptions::empty())
    }

    fn destroy(&self) {
        self.inodes.write().unwrap().clear();
    }

    fn lookup(&self, ctx: Context, parent: u64, name: &CStr) -> io::Result<Entry> {
        let dir = self.inode(parent)?;
        self.entry(ctx, self.root.child(&dir.file, name)?)
    }

    fn forget(&self, _ctx: Context, inode: u64, count: u64) {
        let mut inodes = self.inodes.write().unwrap();
        if let Some(data) = inodes.get(&inode) {
            let remaining = data.refcount.load(Ordering::Relaxed).saturating_sub(count);
            data.refcount.store(remaining, Ordering::Relaxed);
            if remaining == 0 {
                inodes.remove(&inode);
            }
        }
    }

    fn getattr(
        &self,
        ctx: Context,
        inode: u64,
        _handle: Option<u64>,
    ) -> io::Result<(bindings::stat64, Duration)> {
        let data = self.inode(inode)?;
        Ok((
            fstat(
                &ctx,
                PermissionSemantics::LinuxSimplified,
                data.file.as_raw_fd(),
                false,
            )?,
            Duration::ZERO,
        ))
    }

    fn readlink(&self, _ctx: Context, inode: u64) -> io::Result<Vec<u8>> {
        let data = self.inode(inode)?;
        read_link(&data.file)
    }

    fn statfs(&self, _ctx: Context, inode: u64) -> io::Result<bindings::statvfs64> {
        let data = self.inode(inode)?;
        let mut st = MaybeUninit::uninit();
        check_result(unsafe { bindings::fstatvfs64(data.file.as_raw_fd(), st.as_mut_ptr()) })?;
        Ok(unsafe { st.assume_init() })
    }

    fn link(
        &self,
        _ctx: Context,
        _inode: u64,
        _newparent: u64,
        _newname: &CStr,
    ) -> io::Result<Entry> {
        Err(error(libc::EPERM))
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_utils::TestDir;
    use super::*;
    use std::fs;
    use std::os::unix::fs::symlink;

    fn ctx() -> Context {
        Context {
            uid: 1000,
            gid: 1000,
            pid: 1,
        }
    }

    fn filesystem(dir: &TestDir) -> RestrictedFs {
        let fs = RestrictedFs::new(&dir.0, Arc::new(InodeAllocator::new())).unwrap();
        fs.init(FsOptions::all()).unwrap();
        fs
    }

    #[test]
    fn rejects_existing_and_new_hardlinks() {
        let dir = TestDir::new();
        fs::write(dir.0.join("file"), b"contents").unwrap();
        let fs = filesystem(&dir);
        let file = fs.lookup(ctx(), fuse::ROOT_ID, c"file").unwrap();
        assert!(fs.link(ctx(), file.inode, fuse::ROOT_ID, c"new").is_err());
        fs::hard_link(dir.0.join("file"), dir.0.join("other")).unwrap();
        assert!(fs.lookup(ctx(), fuse::ROOT_ID, c"file").is_err());
        assert!(fs.lookup(ctx(), fuse::ROOT_ID, c"other").is_err());
        assert!(fs.getattr(ctx(), file.inode, None).is_err());
        assert!(!dir.0.join("new").exists());
    }

    #[test]
    fn preserves_symlink_identity_and_rejects_symlink_parents() {
        let dir = TestDir::new();
        fs::create_dir(dir.0.join("directory")).unwrap();
        symlink("directory", dir.0.join("link")).unwrap();
        let fs = filesystem(&dir);
        let entry = fs.lookup(ctx(), fuse::ROOT_ID, c"link").unwrap();
        assert_eq!(entry.attr.st_mode & libc::S_IFMT, libc::S_IFLNK);
        assert_eq!(fs.readlink(ctx(), entry.inode).unwrap(), b"directory");
        assert!(fs.lookup(ctx(), entry.inode, c"file").is_err());
        assert_eq!(entry.attr.st_uid, ctx().uid);
        assert_eq!(entry.attr_timeout, Duration::ZERO);
    }

    #[test]
    fn rejects_unlinked_inode_even_after_name_reuse() {
        let dir = TestDir::new();
        fs::write(dir.0.join("file"), b"original").unwrap();
        let fs = filesystem(&dir);
        let entry = fs.lookup(ctx(), fuse::ROOT_ID, c"file").unwrap();
        fs::remove_file(dir.0.join("file")).unwrap();
        fs::write(dir.0.join("file"), b"replacement").unwrap();
        assert!(fs.getattr(ctx(), entry.inode, None).is_err());
        let replacement = fs.lookup(ctx(), fuse::ROOT_ID, c"file").unwrap();
        assert_ne!(entry.inode, replacement.inode);
    }
}
