use std::fmt;

#[derive(Debug)]
pub enum RangeCheckError {
    InputLimbExceedsRange,
}

impl fmt::Display for RangeCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RangeCheckError::InputLimbExceedsRange => write!(f, "Input limb exceeds allowed range"),
        }
    }
}

impl std::error::Error for RangeCheckError {}