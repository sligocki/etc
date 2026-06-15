#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Inc(usize),
    Dec(usize),
    While(usize, Vec<Instr>),
}
