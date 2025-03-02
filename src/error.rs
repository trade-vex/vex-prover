use crate::imt::error::IMTError;
use std::fmt;

#[derive(Debug)]
pub enum GenericError {
    IMT(IMTError),
    InvalidSliceLength(usize, usize),
    InvalidUint8,
}

impl fmt::Display for GenericError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericError::IMT(err) => write!(f, "IMT error: {}", err),
            GenericError::InvalidSliceLength(a, b) => {
                write!(f, "Expected slice length of {} but got {}", a, b)
            }
            GenericError::InvalidUint8 => {
                write!(
                    f,
                    "Each element in the u64 'M31 limbs representation' must be less than 256"
                )
            }
        }
    }
}

impl std::error::Error for GenericError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            GenericError::IMT(err) => Some(err),
            _ => Some(self),
        }
    }
}
