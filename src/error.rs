use stwo_prover::core::prover::VerificationError;

use crate::imt::error::IMTError;
use std::fmt;

#[derive(Debug)]
pub enum GenericError {
    IMT(IMTError),
    InvalidSliceLength(usize, usize),
    InvalidUint8,
    InvalidLogupSum,
    Stark(VerificationError),
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
            GenericError::InvalidLogupSum => {
                write!(f, "Total Lookup sum must be zero")
            }
            GenericError::Stark(err) => {
                write!(f, "Stark error: {}", err)
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

#[derive(Debug)]
pub enum VexVerificationError {
    InvalidLogupSum,
    Stark(VerificationError),
}

impl fmt::Display for VexVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VexVerificationError::InvalidLogupSum => {
                write!(f, "Total Lookup sum must be zero")
            }
            VexVerificationError::Stark(err) => {
                write!(f, "Stark error: {}", err)
            }
        }
    }
}

impl std::error::Error for VexVerificationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            VexVerificationError::Stark(err) => Some(err),
            _ => Some(self),
        }
    }
}
