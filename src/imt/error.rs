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
    NotAPartialMatch,
    CannotCancelInactive,
    AdditionOverflow,
}

impl fmt::Display for IMTError {
    /// Formats the `IMTError` enum into a human-readable error message.
    ///
    /// Converts each error variant into a descriptive string, including any associated data, for display purposes.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::imt::error::IMTError;
    /// use std::fmt;
    ///
    /// let err = IMTError::LeafNotFound;
    /// assert_eq!(format!("{}", err), "Leaf not found");
    ///
    /// let err = IMTError::OperationFailed("timeout".to_string());
    /// assert_eq!(format!("{}", err), "Operation failed: timeout");
    /// ```
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
            IMTError::NotAPartialMatch => write!(f, "Not a partial match"),
            IMTError::CannotCancelInactive => write!(f, "Cannot cancel the inactive leaf"),
            IMTError::AdditionOverflow  => write!(f, "Addition Overflow for u64"),
        }
    }
}

impl std::error::Error for IMTError {}
