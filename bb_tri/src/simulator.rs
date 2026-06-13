use std::collections::HashMap;
use crate::tm::{Direction, State, TuringMachine};

#[derive(Debug, Clone)]
pub struct Tape {
    // The default symbol is 0. We store non-zero symbols in a hash map.
    // The position is uniquely represented by the shortest path from origin.
    // In this path, no two adjacent elements are the same color.
    pub grid: HashMap<Vec<Direction>, u8>,
}

impl Tape {
    pub fn new() -> Self {
        Self {
            grid: HashMap::new(),
        }
    }

    pub fn read(&self, pos: &[Direction]) -> u8 {
        *self.grid.get(pos).unwrap_or(&0)
    }

    pub fn write(&mut self, pos: &[Direction], symbol: u8) {
        if symbol == 0 {
            self.grid.remove(pos);
        } else {
            self.grid.insert(pos.to_vec(), symbol);
        }
    }

    pub fn score(&self) -> usize {
        self.grid.values().filter(|&&v| v != 0).count()
    }
}

pub enum SimResult {
    Halt(u64, usize), // Halts after N steps, leaving S score
    LimitReached,     // Reached step limit
    UndefinedTrans,   // Hit an undefined transition (used in enumerator)
}

#[derive(Clone)]
pub struct Simulator {
    pub tape: Tape,
    pub head: Vec<Direction>,
    pub state: State,
    pub steps: u64,
}

impl Simulator {
    pub fn new() -> Self {
        Self {
            tape: Tape::new(),
            head: Vec::new(),
            state: State::Active(0),
            steps: 0,
        }
    }

    pub fn run(&mut self, tm: &TuringMachine, step_limit: u64) -> SimResult {
        while self.steps < step_limit {
            if let State::Halt = self.state {
                return SimResult::Halt(self.steps, self.tape.score());
            }

            let State::Active(curr_state) = self.state else {
                unreachable!()
            };

            let symbol = self.tape.read(&self.head);

            let trans = match tm.get_transition(curr_state, symbol) {
                Some(t) => t,
                None => return SimResult::UndefinedTrans,
            };

            // 1. Write symbol
            self.tape.write(&self.head, trans.symbol);

            // 2. Move
            if let Some(&last_dir) = self.head.last() {
                if last_dir == trans.dir {
                    self.head.pop();
                } else {
                    self.head.push(trans.dir);
                }
            } else {
                self.head.push(trans.dir);
            }

            // 3. Update state
            self.state = trans.next_state;
            self.steps += 1;
        }

        // Check if we just halted exactly at the limit
        if let State::Halt = self.state {
            return SimResult::Halt(self.steps, self.tape.score());
        }

        SimResult::LimitReached
    }
}
