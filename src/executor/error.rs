pub enum AddOperationError {
    InputLimbExceedsRange,
    FinalLimbOverflow,
}
#[derive(Debug)]
pub enum RangeCheckError {
    InputLimbExceedsRange,
}