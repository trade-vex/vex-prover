use std::fmt;

#[derive(Debug)]
pub enum IMTError {
    CannotCancelFirstLeaf,
    CannotUpdateFirstLeaf,
    LowLeafNotFound,
    LeafNotFound,
    InvalidNode,
    OperationFailed(String),
    InsufficientVolumeToFill(u64, u64),
    InvalidU8Pair(u32, u32),
    InvalidOrder,
    CannotCancelInactive,
}

impl fmt::Display for IMTError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IMTError::CannotCancelFirstLeaf => write!(f, "Cannot cancel the first leaf"),
            IMTError::CannotUpdateFirstLeaf => write!(f, "Cannot update the first leaf"),
            IMTError::LeafNotFound => write!(f, "Leaf not found"),
            IMTError::LowLeafNotFound => write!(f, "Low leaf not found"),
            IMTError::InvalidNode => write!(f, "Invalid node"),
            IMTError::OperationFailed(reason) => write!(f, "Operation failed: {}", reason),
            IMTError::InsufficientVolumeToFill(volume, available) => {
                write!(f, "Insufficient volume to fill: {} > {}", volume, available)
            }
            IMTError::InvalidU8Pair(a, b) => write!(f, "Invalid u8 pair: {} {}", a, b),
            IMTError::InvalidOrder => write!(f, "Volume, Price, Time cannot be zero"),
            IMTError::CannotCancelInactive => write!(f, "Cannot cancel the inactive leaf"),
        }
    }
}

impl std::error::Error for IMTError {}
