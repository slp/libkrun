use libc;

pub const LINUX_ENODATA: libc::c_int = 61;
pub const LINUX_ENOSYS: libc::c_int = 38;

#[cfg(target_os = "macos")]
pub type stat64 = libc::stat;
#[cfg(target_os = "linux")]
pub use libc::stat64;

#[cfg(target_os = "macos")]
pub type off64_t = libc::off_t;
#[cfg(target_os = "linux")]
pub use libc::off64_t;

#[cfg(target_os = "macos")]
pub type statvfs64 = libc::statvfs;
#[cfg(target_os = "linux")]
pub use libc::statvfs64;

#[cfg(target_os = "macos")]
pub type ino64_t = libc::ino_t;
#[cfg(target_os = "linux")]
pub use libc::ino64_t;

#[cfg(target_os = "linux")]
pub unsafe fn pread64(
    fd: libc::c_int,
    buf: *mut libc::c_void,
    count: libc::size_t,
    offset: off64_t,
) -> libc::ssize_t {
    libc::pread64(fd, buf, count, offset)
}
#[cfg(target_os = "macos")]
pub unsafe fn pread64(
    fd: libc::c_int,
    buf: *mut libc::c_void,
    count: libc::size_t,
    offset: off64_t,
) -> libc::ssize_t {
    libc::pread(fd, buf, count, offset)
}

#[cfg(target_os = "linux")]
pub unsafe fn preadv64(
    fd: libc::c_int,
    iov: *const libc::iovec,
    iovcnt: libc::c_int,
    offset: off64_t,
) -> libc::ssize_t {
    libc::preadv64(fd, iov, iovcnt, offset)
}
#[cfg(target_os = "macos")]
pub unsafe fn preadv64(
    fd: libc::c_int,
    iov: *const libc::iovec,
    iovcnt: libc::c_int,
    offset: off64_t,
) -> libc::ssize_t {
    libc::preadv(fd, iov, iovcnt, offset)
}

#[cfg(target_os = "linux")]
pub unsafe fn pwrite64(
    fd: libc::c_int,
    buf: *const libc::c_void,
    count: libc::size_t,
    offset: off64_t,
) -> libc::ssize_t {
    libc::pwrite64(fd, buf, count, offset)
}
#[cfg(target_os = "macos")]
pub unsafe fn pwrite64(
    fd: libc::c_int,
    buf: *const libc::c_void,
    count: libc::size_t,
    offset: off64_t,
) -> libc::ssize_t {
    libc::pwrite(fd, buf, count, offset)
}

#[cfg(target_os = "linux")]
pub unsafe fn pwritev64(
    fd: libc::c_int,
    iov: *const libc::iovec,
    iovcnt: libc::c_int,
    offset: off64_t,
) -> libc::ssize_t {
    libc::pwritev64(fd, iov, iovcnt, offset)
}
#[cfg(target_os = "macos")]
pub unsafe fn pwritev64(
    fd: libc::c_int,
    iov: *const libc::iovec,
    iovcnt: libc::c_int,
    offset: off64_t,
) -> libc::ssize_t {
    libc::pwritev(fd, iov, iovcnt, offset)
}

#[cfg(target_os = "linux")]
pub unsafe fn fstatat64(
    dirfd: libc::c_int,
    pathname: *const libc::c_char,
    buf: *mut stat64,
    flags: libc::c_int,
) -> libc::c_int {
    libc::fstatat64(dirfd, pathname, buf, flags)
}
#[cfg(target_os = "macos")]
pub unsafe fn fstatat64(
    dirfd: libc::c_int,
    pathname: *const libc::c_char,
    buf: *mut stat64,
    flags: libc::c_int,
) -> libc::c_int {
    libc::fstatat(dirfd, pathname, buf, flags)
}

#[cfg(target_os = "linux")]
pub unsafe fn fallocate64(
    fd: libc::c_int,
    mode: libc::c_int,
    offset: off64_t,
    len: off64_t,
) -> libc::c_int {
    libc::fallocate64(fd, mode, offset, len)
}
#[cfg(target_os = "macos")]
pub unsafe fn fallocate64(
    fd: libc::c_int,
    mode: libc::c_int,
    offset: off64_t,
    len: off64_t,
) -> libc::c_int {
    -libc::ENOSYS
}

#[cfg(target_os = "linux")]
pub unsafe fn ftruncate64(fd: libc::c_int, length: off64_t) -> libc::c_int {
    libc::ftruncate64(fd, length)
}
#[cfg(target_os = "macos")]
pub unsafe fn ftruncate64(fd: libc::c_int, length: off64_t) -> libc::c_int {
    libc::ftruncate(fd, length)
}

#[cfg(target_os = "linux")]
pub unsafe fn lseek64(fd: libc::c_int, offset: off64_t, whence: libc::c_int) -> off64_t {
    libc::lseek64(fd, offset, whence)
}
#[cfg(target_os = "macos")]
pub unsafe fn lseek64(fd: libc::c_int, offset: off64_t, whence: libc::c_int) -> off64_t {
    libc::lseek(fd, offset, whence)
}

#[cfg(target_os = "linux")]
pub unsafe fn statvfs64(path: *const libc::c_char, buf: *mut statvfs64) -> libc::c_int {
    libc::statvfs64(path, buf)
}
#[cfg(target_os = "macos")]
pub unsafe fn statvfs64(path: *const libc::c_char, buf: *mut statvfs64) -> libc::c_int {
    libc::statvfs(path, buf)
}

#[cfg(target_os = "linux")]
pub unsafe fn fstatvfs64(fd: libc::c_int, buf: *mut statvfs64) -> libc::c_int {
    libc::fstatvfs64(fd, buf)
}
#[cfg(target_os = "macos")]
pub unsafe fn fstatvfs64(fd: libc::c_int, buf: *mut statvfs64) -> libc::c_int {
    libc::fstatvfs(fd, buf)
}

#[cfg(target_os = "linux")]
pub unsafe fn mknodat(
    dirfd: libc::c_int,
    pathname: *const libc::c_char,
    mode: libc::mode_t,
    dev: libc::dev_t,
) -> libc::c_int {
    libc::mknodat(dirfd, pathname, mode, dev)
}
#[cfg(target_os = "macos")]
pub unsafe fn mknodat(
    dirfd: libc::c_int,
    pathname: *const libc::c_char,
    mode: libc::mode_t,
    dev: u64,
) -> libc::c_int {
    -libc::ENOSYS
}
