use crate::tm::{Direction, State, TuringMachine};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub symbol: u8,
    pub r: u32,
    pub g: u32,
    pub b: u32,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            symbol: 0,
            r: u32::MAX,
            g: u32::MAX,
            b: u32::MAX,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tape {
    pub nodes: Vec<Node>,
}

impl Tape {
    pub fn new() -> Self {
        Self {
            nodes: vec![Node::default()],
        }
    }

    pub fn score(&self) -> u32 {
        self.nodes.iter().filter(|n| n.symbol != 0).count() as u32
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimResult {
    Halt(u64, u32), // steps, score
    LimitReached,
    UndefinedTrans,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Simulator {
    pub tape: Tape,
    pub head: u32,
    pub state: State,
    pub steps: u64,
}

impl Simulator {
    pub fn new() -> Self {
        Self {
            tape: Tape::new(),
            head: 0,
            state: State::Active(0),
            steps: 0,
        }
    }

    pub fn run(&mut self, tm: &TuringMachine, step_limit: u64) -> SimResult {
        while self.steps < step_limit {
            if self.state == State::Halt {
                return SimResult::Halt(self.steps, self.tape.score());
            }

            let s = match self.state {
                State::Active(s) => s,
                State::Halt => unreachable!(),
            };

            let curr = self.head as usize;
            let sym = self.tape.nodes[curr].symbol;

            let trans = match tm.get_transition(s, sym) {
                Some(t) => t,
                None => return SimResult::UndefinedTrans,
            };

            self.tape.nodes[curr].symbol = trans.symbol;
            self.state = trans.next_state;

            let next_idx = match trans.dir {
                Direction::R => self.tape.nodes[curr].r,
                Direction::G => self.tape.nodes[curr].g,
                Direction::B => self.tape.nodes[curr].b,
            };

            if next_idx == u32::MAX {
                let new_idx = self.tape.nodes.len() as u32;
                self.tape.nodes.push(Node::default());

                match trans.dir {
                    Direction::R => {
                        self.tape.nodes[curr].r = new_idx;
                        self.tape.nodes[new_idx as usize].r = curr as u32;
                    }
                    Direction::G => {
                        self.tape.nodes[curr].g = new_idx;
                        self.tape.nodes[new_idx as usize].g = curr as u32;
                    }
                    Direction::B => {
                        self.tape.nodes[curr].b = new_idx;
                        self.tape.nodes[new_idx as usize].b = curr as u32;
                    }
                }
                self.head = new_idx;
            } else {
                self.head = next_idx;
            }

            self.steps += 1;
        }

        SimResult::LimitReached
    }

    pub fn run_with_transcript(
        &mut self,
        tm: &TuringMachine,
        step_limit: u64,
    ) -> (SimResult, Vec<(u8, u8)>) {
        let mut transcript = Vec::new();

        while self.steps < step_limit {
            if self.state == State::Halt {
                return (SimResult::Halt(self.steps, self.tape.score()), transcript);
            }

            let s = match self.state {
                State::Active(s) => s,
                State::Halt => unreachable!(),
            };

            let curr = self.head as usize;
            let sym = self.tape.nodes[curr].symbol;

            transcript.push((s, sym));

            let trans = match tm.get_transition(s, sym) {
                Some(t) => t,
                None => return (SimResult::UndefinedTrans, transcript),
            };

            self.tape.nodes[curr].symbol = trans.symbol;
            self.state = trans.next_state;

            let next_idx = match trans.dir {
                Direction::R => self.tape.nodes[curr].r,
                Direction::G => self.tape.nodes[curr].g,
                Direction::B => self.tape.nodes[curr].b,
            };

            if next_idx == u32::MAX {
                let new_idx = self.tape.nodes.len() as u32;
                self.tape.nodes.push(Node::default());

                match trans.dir {
                    Direction::R => {
                        self.tape.nodes[curr].r = new_idx;
                        self.tape.nodes[new_idx as usize].r = curr as u32;
                    }
                    Direction::G => {
                        self.tape.nodes[curr].g = new_idx;
                        self.tape.nodes[new_idx as usize].g = curr as u32;
                    }
                    Direction::B => {
                        self.tape.nodes[curr].b = new_idx;
                        self.tape.nodes[new_idx as usize].b = curr as u32;
                    }
                }
                self.head = new_idx;
            } else {
                self.head = next_idx;
            }

            self.steps += 1;
        }

        (SimResult::LimitReached, transcript)
    }
}
