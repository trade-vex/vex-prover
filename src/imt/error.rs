use std::fmt;

#[derive(Debug)]
pub enum IMTError {
    CannotCancelFirstLeaf,
    CannotUpdateFirstLeaf,
    LowLeafNotFound,
    LeafNotFound,
    InvalidNode,
    OperationFailed(String),
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
        }
    }
}

impl std::error::Error for IMTError {}
