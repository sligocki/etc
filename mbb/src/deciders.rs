use crate::program::Program;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeciderResult {
    Halt,
    NonHalt,
    Unknown,
}

pub trait Decider {
    fn decide(&self, prog: &Program) -> DeciderResult;
}
