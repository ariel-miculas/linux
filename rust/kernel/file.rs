// SPDX-License-Identifier: GPL-2.0

//! Files and file descriptors.
//!
//! C headers: [`include/linux/fs.h`](../../../../include/linux/fs.h) and
//! [`include/linux/file.h`](../../../../include/linux/file.h)

use crate::{
    bindings,
    error::{code::*, from_err_ptr, Error, Result},
    mount::Vfsmount,
    str::CStr,
    types::{ARef, AlwaysRefCounted, Opaque},
};
use alloc::vec::Vec;
use core::ptr;

/// Flags associated with a [`File`].
pub mod flags {
    /// File is opened in append mode.
    pub const O_APPEND: u32 = bindings::O_APPEND;

    /// Signal-driven I/O is enabled.
    pub const O_ASYNC: u32 = bindings::FASYNC;

    /// Close-on-exec flag is set.
    pub const O_CLOEXEC: u32 = bindings::O_CLOEXEC;

    /// File was created if it didn't already exist.
    pub const O_CREAT: u32 = bindings::O_CREAT;

    /// Direct I/O is enabled for this file.
    pub const O_DIRECT: u32 = bindings::O_DIRECT;

    /// File must be a directory.
    pub const O_DIRECTORY: u32 = bindings::O_DIRECTORY;

    /// Like [`O_SYNC`] except metadata is not synced.
    pub const O_DSYNC: u32 = bindings::O_DSYNC;

    /// Ensure that this file is created with the `open(2)` call.
    pub const O_EXCL: u32 = bindings::O_EXCL;

    /// Large file size enabled (`off64_t` over `off_t`).
    pub const O_LARGEFILE: u32 = bindings::O_LARGEFILE;

    /// Do not update the file last access time.
    pub const O_NOATIME: u32 = bindings::O_NOATIME;

    /// File should not be used as process's controlling terminal.
    pub const O_NOCTTY: u32 = bindings::O_NOCTTY;

    /// If basename of path is a symbolic link, fail open.
    pub const O_NOFOLLOW: u32 = bindings::O_NOFOLLOW;

    /// File is using nonblocking I/O.
    pub const O_NONBLOCK: u32 = bindings::O_NONBLOCK;

    /// Also known as `O_NDELAY`.
    ///
    /// This is effectively the same flag as [`O_NONBLOCK`] on all architectures
    /// except SPARC64.
    pub const O_NDELAY: u32 = bindings::O_NDELAY;

    /// Used to obtain a path file descriptor.
    pub const O_PATH: u32 = bindings::O_PATH;

    /// Write operations on this file will flush data and metadata.
    pub const O_SYNC: u32 = bindings::O_SYNC;

    /// This file is an unnamed temporary regular file.
    pub const O_TMPFILE: u32 = bindings::O_TMPFILE;

    /// File should be truncated to length 0.
    pub const O_TRUNC: u32 = bindings::O_TRUNC;

    /// Bitmask for access mode flags.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::file;
    /// # fn do_something() {}
    /// # let flags = 0;
    /// if (flags & file::flags::O_ACCMODE) == file::flags::O_RDONLY {
    ///     do_something();
    /// }
    /// ```
    pub const O_ACCMODE: u32 = bindings::O_ACCMODE;

    /// File is read only.
    pub const O_RDONLY: u32 = bindings::O_RDONLY;

    /// File is write only.
    pub const O_WRONLY: u32 = bindings::O_WRONLY;

    /// File can be both read and written.
    pub const O_RDWR: u32 = bindings::O_RDWR;
}

/// Wraps the kernel's `struct file`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `get_file` ensures that the
/// allocation remains valid at least until the matching call to `fput`.
#[repr(transparent)]
pub struct File(Opaque<bindings::file>);

// SAFETY: By design, the only way to access a `File` is via an immutable reference or an `ARef`.
// This means that the only situation in which a `File` can be accessed mutably is when the
// refcount drops to zero and the destructor runs. It is safe for that to happen on any thread, so
// it is ok for this type to be `Send`.
unsafe impl Send for File {}

// SAFETY: It's OK to access `File` through shared references from other threads because we're
// either accessing properties that don't change or that are properly synchronised by C code.
unsafe impl Sync for File {}

impl File {
    /// Constructs a new `struct file` wrapper from a file descriptor.
    ///
    /// The file descriptor belongs to the current process.
    pub fn from_fd(fd: u32) -> Result<ARef<Self>, BadFdError> {
        // SAFETY: FFI call, there are no requirements on `fd`.
        let ptr = ptr::NonNull::new(unsafe { bindings::fget(fd) }).ok_or(BadFdError)?;

        // SAFETY: `fget` increments the refcount before returning.
        Ok(unsafe { ARef::from_raw(ptr.cast()) })
    }

    /// Creates a reference to a [`File`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `ptr` points at a valid file and that its refcount does not
    /// reach zero until after the end of the lifetime 'a.
    pub unsafe fn from_ptr<'a>(ptr: *const bindings::file) -> &'a File {
        // SAFETY: The safety requirements guarantee the validity of the dereference, while the
        // `File` type being transparent makes the cast ok.
        unsafe { &*ptr.cast() }
    }

    /// Returns the flags associated with the file.
    ///
    /// The flags are a combination of the constants in [`flags`].
    pub fn flags(&self) -> u32 {
        // SAFETY: The file is valid because the shared reference guarantees a nonzero refcount.
        //
        // This uses a volatile read because C code may be modifying this field in parallel using
        // non-atomic unsynchronized writes. This corresponds to how the C macro READ_ONCE is
        // implemented.
        unsafe { core::ptr::addr_of!((*self.0.get()).f_flags).read_volatile() }
    }
}

// SAFETY: The type invariants guarantee that `File` is always ref-counted.
unsafe impl AlwaysRefCounted for File {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::get_file(self.0.get()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::fput(obj.cast().as_ptr()) }
    }
}

/// A newtype over file, specific to regular files
pub struct RegularFile(ARef<File>);
impl RegularFile {
    /// Creates a new instance of Self if the file is a regular file
    ///
    /// # Safety
    ///
    /// The caller must ensure file_ptr.f_inode is initialized to a valid pointer (e.g. file_ptr is
    /// a pointer returned by path_openat); It must also ensure that file_ptr's reference count was
    /// incremented at least once
    unsafe fn create_if_regular(file_ptr: *mut bindings::file) -> Result<RegularFile> {
        let file_ptr = ptr::NonNull::new(file_ptr).ok_or(ENOENT)?;
        // SAFETY: file_ptr is a NonNull pointer
        let inode = unsafe { core::ptr::addr_of!((*file_ptr.as_ptr()).f_inode).read() };
        // SAFETY: the caller must ensure f_inode is initialized to a valid pointer
        let inode_mode = unsafe { (*inode).i_mode as u32 };
        if bindings::S_IFMT & inode_mode != bindings::S_IFREG {
            return Err(EINVAL);
        }
        // SAFETY: the safety requirements state that file_ptr's reference count was incremented at
        // least once
        Ok(RegularFile(unsafe { ARef::from_raw(file_ptr.cast()) }))
    }
    /// Constructs a new [`struct file`] wrapper from a path.
    pub fn from_path(filename: &CStr, flags: i32, mode: u16) -> Result<Self> {
        // SAFETY: filename is a reference, so it's a valid pointer
        let file_ptr = unsafe {
            from_err_ptr(bindings::filp_open(
                filename.as_ptr().cast::<i8>(),
                flags,
                mode,
            ))?
        };

        // SAFETY: `filp_open` initializes the refcount with 1
        unsafe { Self::create_if_regular(file_ptr) }
    }

    /// Constructs a new [`struct file`] wrapper from a path and a vfsmount.
    pub fn from_path_in_root_mnt(
        mount: &Vfsmount,
        filename: &CStr,
        flags: i32,
        mode: u16,
    ) -> Result<Self> {
        let mnt = mount.get();
        // construct a path from vfsmount, see file_open_root_mnt
        let raw_path = bindings::path {
            mnt,
            // SAFETY: Vfsmount structure stores a valid vfsmount object
            dentry: unsafe { (*mnt).mnt_root },
        };
        let file_ptr = unsafe {
            // SAFETY: raw_path and filename are both references
            from_err_ptr(bindings::file_open_root(
                &raw_path,
                filename.as_ptr().cast::<i8>(),
                flags,
                mode,
            ))?
        };
        // SAFETY: `file_open_root` initializes the refcount with 1
        unsafe { Self::create_if_regular(file_ptr) }
    }

    /// Read from the file into the specified buffer
    pub fn read_with_offset(&self, buf: &mut [u8], offset: u64) -> Result<usize> {
        // kernel_read_file expects a pointer to a "void *" buffer
        let mut ptr_to_buf = buf.as_mut_ptr() as *mut core::ffi::c_void;
        // Unless we give a non-null pointer to the file size:
        // 1. we cannot give a non-zero value for the offset
        // 2. we cannot have offset 0 and buffer_size > file_size
        let mut file_size = 0;

        // SAFETY: 'file' is valid because it's taken from Self, 'buf' and 'file_size` are
        // references to the stack variables 'ptr_to_buf' and 'file_size'; ptr_to_buf is also
        // a pointer to a valid buffer that was obtained from a reference
        let result = unsafe {
            bindings::kernel_read_file(
                self.0 .0.get(),
                offset.try_into()?,
                &mut ptr_to_buf,
                buf.len(),
                &mut file_size,
                bindings::kernel_read_file_id_READING_UNKNOWN,
            )
        };

        // kernel_read_file returns the number of bytes read on success or negative on error.
        if result < 0 {
            return Err(Error::from_errno(result.try_into()?));
        }

        Ok(result.try_into()?)
    }

    /// Allocate and return a vector containing the contents of the entire file
    pub fn read_to_end(&self) -> Result<Vec<u8>> {
        let file_size = self.get_file_size()?;
        let mut buffer = Vec::try_with_capacity(file_size)?;
        buffer.try_resize(file_size, 0)?;
        self.read_with_offset(&mut buffer, 0)?;
        Ok(buffer)
    }

    fn get_file_size(&self) -> Result<usize> {
        // SAFETY: 'file' is valid because it's taken from Self
        let file_size = unsafe { bindings::i_size_read((*self.0 .0.get()).f_inode) };

        if file_size < 0 {
            return Err(EINVAL);
        }

        Ok(file_size.try_into()?)
    }
}

/// Represents the EBADF error code.
///
/// Used for methods that can only fail with EBADF.
pub struct BadFdError;

impl From<BadFdError> for Error {
    fn from(_: BadFdError) -> Error {
        EBADF
    }
}
