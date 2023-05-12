use alloc::collections::TryReserveError;
use core::ffi::c_int;
use core::fmt::{self, Display};
use kernel::prelude::EINVAL;

pub(crate) enum WireFormatError {
    InvalidSerializedData,
    KernelError(kernel::error::Error),
    TryReserveError(TryReserveError),
    CapnpError(capnp::Error),
    FromIntError(core::num::TryFromIntError),
    FromSliceError(core::array::TryFromSliceError),
    HexError(hex::FromHexError),
}

impl WireFormatError {
    pub(crate) fn to_errno(&self) -> c_int {
        match self {
            WireFormatError::InvalidSerializedData => kernel::error::Error::to_errno(EINVAL),
            WireFormatError::KernelError(e) => kernel::error::Error::to_errno(*e),
            WireFormatError::TryReserveError(_) => kernel::error::Error::to_errno(EINVAL),
            WireFormatError::CapnpError(_) => kernel::error::Error::to_errno(EINVAL),
            WireFormatError::FromIntError(_) => kernel::error::Error::to_errno(EINVAL),
            WireFormatError::FromSliceError(_) => kernel::error::Error::to_errno(EINVAL),
            WireFormatError::HexError(_) => kernel::error::Error::to_errno(EINVAL),
        }
    }

    pub(crate) fn from_errno(errno: kernel::error::Error) -> Self {
        Self::KernelError(errno)
    }
}

impl Display for WireFormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WireFormatError::InvalidSerializedData => f.write_str("invalid serialized data"),
            WireFormatError::KernelError(e) => {
                f.write_fmt(format_args!("Kernel error {}", e.to_errno()))
            }
            WireFormatError::TryReserveError(_) => f.write_str("TryReserveError"),
            WireFormatError::CapnpError(_) => f.write_str("Capnp error"),
            WireFormatError::FromIntError(_) => f.write_str("TryFromIntError"),
            WireFormatError::FromSliceError(_) => f.write_str("TryFromSliceError"),
            WireFormatError::HexError(_) => f.write_str("HexError"),
        }
    }
}

pub(crate) type Result<T> = kernel::error::Result<T, WireFormatError>;

// TODO figure out how to use thiserror
#[allow(unused_qualifications)]
impl core::convert::From<kernel::error::Error> for WireFormatError {
    #[allow(deprecated)]
    fn from(source: kernel::error::Error) -> Self {
        WireFormatError::KernelError(source)
    }
}

#[allow(unused_qualifications)]
impl core::convert::From<TryReserveError> for WireFormatError {
    #[allow(deprecated)]
    fn from(source: TryReserveError) -> Self {
        WireFormatError::TryReserveError(source)
    }
}

#[allow(unused_qualifications)]
impl core::convert::From<capnp::Error> for WireFormatError {
    #[allow(deprecated)]
    fn from(source: capnp::Error) -> Self {
        WireFormatError::CapnpError(source)
    }
}

#[allow(unused_qualifications)]
impl core::convert::From<core::array::TryFromSliceError> for WireFormatError {
    #[allow(deprecated)]
    fn from(source: core::array::TryFromSliceError) -> Self {
        WireFormatError::FromSliceError(source)
    }
}

#[allow(unused_qualifications)]
impl core::convert::From<core::num::TryFromIntError> for WireFormatError {
    #[allow(deprecated)]
    fn from(source: core::num::TryFromIntError) -> Self {
        WireFormatError::FromIntError(source)
    }
}

impl core::convert::From<hex::FromHexError> for WireFormatError {
    #[allow(deprecated)]
    fn from(source: hex::FromHexError) -> Self {
        WireFormatError::HexError(source)
    }
}

#[allow(unused_qualifications)]
impl core::convert::From<WireFormatError> for kernel::error::Error {
    #[allow(deprecated)]
    fn from(source: WireFormatError) -> Self {
        kernel::error::Error::from_errno(source.to_errno())
    }
}
