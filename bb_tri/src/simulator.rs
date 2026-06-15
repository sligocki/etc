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

    pub fn space(&self) -> u32 {
        self.nodes.len() as u32
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfReason {
    Stationary,
    Translated,
    NoPath,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimResult {
    Halt(u64, u32), // steps, space
    LimitReached,
    UndefinedTrans,
    Infinite(InfReason),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct DeciderOptions {
    pub stationary: bool,
    pub translated: bool,
    pub nopath: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Simulator {
    pub tape: Tape,
    pub head: u32,
    pub state: State,
    pub steps: u64,
    pub blank_entries: Vec<(State, Direction, u32)>,
    
    // Brent's cycle detection variables
    pub brent_power: u64,
    pub brent_lam: u64,
    pub saved_head: u32,
    pub saved_state: State,
    pub saved_symbols: Vec<u8>,
    pub deciders: DeciderOptions,
    pub can_reach_halt: Option<Vec<bool>>,
}

impl Simulator {
    pub fn new(deciders: DeciderOptions) -> Self {
        Self {
            tape: Tape::new(),
            head: 0,
            state: State::Active(0),
            steps: 0,
            blank_entries: Vec::new(),
            brent_power: 1,
            brent_lam: 1,
            saved_head: 0,
            saved_state: State::Active(0),
            saved_symbols: vec![0],
            deciders,
            can_reach_halt: None,
        }
    }

    pub fn run(&mut self, tm: &TuringMachine, step_limit: u64) -> SimResult {
        if self.deciders.nopath && self.can_reach_halt.is_none() {
            self.can_reach_halt = Some(compute_halt_reachable(tm));
        }

        while self.steps < step_limit {
            let s = match self.state {
                State::Active(s) => {
                    if self.deciders.nopath {
                        if let Some(reach) = &self.can_reach_halt {
                            if !reach[s as usize] {
                                return SimResult::Infinite(InfReason::NoPath);
                            }
                        }
                    }
                    s
                },
                State::Halt => return SimResult::Halt(self.steps, self.tape.space()),
            };

            let curr = self.head as usize;
            let sym = self.tape.nodes[curr].symbol;

            let trans = match tm.get_transition(s, sym) {
                Some(t) => t,
                None => return SimResult::UndefinedTrans,
            };

            if self.deciders.stationary {
                if self.steps > 0 && self.head == self.saved_head && self.state == self.saved_state && self.tape.nodes.len() == self.saved_symbols.len() {
                    if self.tape.nodes.iter().zip(self.saved_symbols.iter()).all(|(n, &s)| n.symbol == s) {
                        return SimResult::Infinite(InfReason::Stationary);
                    }
                }

                if self.brent_lam == self.brent_power {
                    self.saved_head = self.head;
                    self.saved_state = self.state;
                    self.saved_symbols.clear();
                    self.saved_symbols.extend(self.tape.nodes.iter().map(|n| n.symbol));
                    self.brent_power *= 2;
                    self.brent_lam = 0;
                }
                self.brent_lam += 1;
            }

            if self.deciders.translated {
                while let Some(&(_, _, node_idx)) = self.blank_entries.last() {
                    if node_idx > self.head {
                        self.blank_entries.pop();
                    } else {
                        break;
                    }
                }
            }

            self.tape.nodes[curr].symbol = trans.symbol;
            self.state = trans.next_state;

            if self.state == State::Halt {
                self.steps += 1;
                return SimResult::Halt(self.steps, self.tape.space());
            }

            let next_idx = match trans.dir {
                Direction::R => self.tape.nodes[curr].r,
                Direction::G => self.tape.nodes[curr].g,
                Direction::B => self.tape.nodes[curr].b,
            };

            if next_idx == u32::MAX {
                let new_idx = self.tape.nodes.len() as u32;
                
                if self.deciders.translated {
                    if self.blank_entries.iter().any(|(st, dir, _)| *st == trans.next_state && *dir == trans.dir) {
                        return SimResult::Infinite(InfReason::Translated);
                    }
                    self.blank_entries.push((trans.next_state, trans.dir, new_idx));
                }

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
        if self.deciders.nopath && self.can_reach_halt.is_none() {
            self.can_reach_halt = Some(compute_halt_reachable(tm));
        }

        let mut transcript = Vec::new();

        while self.steps < step_limit {
            let s = match self.state {
                State::Active(s) => {
                    if self.deciders.nopath {
                        if let Some(reach) = &self.can_reach_halt {
                            if !reach[s as usize] {
                                return (SimResult::Infinite(InfReason::NoPath), transcript);
                            }
                        }
                    }
                    s
                },
                State::Halt => return (SimResult::Halt(self.steps, self.tape.space()), transcript),
            };

            let curr = self.head as usize;
            let sym = self.tape.nodes[curr].symbol;

            let trans = match tm.get_transition(s, sym) {
                Some(t) => t,
                None => return (SimResult::UndefinedTrans, transcript),
            };

            if self.deciders.stationary {
                if self.steps > 0 && self.head == self.saved_head && self.state == self.saved_state && self.tape.nodes.len() == self.saved_symbols.len() {
                    if self.tape.nodes.iter().zip(self.saved_symbols.iter()).all(|(n, &s)| n.symbol == s) {
                        return (SimResult::Infinite(InfReason::Stationary), transcript);
                    }
                }

                if self.brent_lam == self.brent_power {
                    self.saved_head = self.head;
                    self.saved_state = self.state;
                    self.saved_symbols.clear();
                    self.saved_symbols.extend(self.tape.nodes.iter().map(|n| n.symbol));
                    self.brent_power *= 2;
                    self.brent_lam = 0;
                }
                self.brent_lam += 1;
            }

            if self.deciders.translated {
                while let Some(&(_, _, node_idx)) = self.blank_entries.last() {
                    if node_idx > self.head {
                        self.blank_entries.pop();
                    } else {
                        break;
                    }
                }
            }

            transcript.push((s, sym));

            self.tape.nodes[curr].symbol = trans.symbol;
            self.state = trans.next_state;

            if self.state == State::Halt {
                self.steps += 1;
                return (SimResult::Halt(self.steps, self.tape.space()), transcript);
            }

            let next_idx = match trans.dir {
                Direction::R => self.tape.nodes[curr].r,
                Direction::G => self.tape.nodes[curr].g,
                Direction::B => self.tape.nodes[curr].b,
            };

            if next_idx == u32::MAX {
                let new_idx = self.tape.nodes.len() as u32;
                
                if self.deciders.translated {
                    if self.blank_entries.iter().any(|(st, dir, _)| *st == trans.next_state && *dir == trans.dir) {
                        return (SimResult::Infinite(InfReason::Translated), transcript);
                    }
                    self.blank_entries.push((trans.next_state, trans.dir, new_idx));
                }

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

pub fn compute_halt_reachable(tm: &TuringMachine) -> Vec<bool> {
    let mut reachable = vec![false; tm.num_states as usize];
    let mut changed = true;

    while changed {
        changed = false;
        for s in 0..tm.num_states {
            if reachable[s as usize] {
                continue;
            }
            
            for sym in 0..tm.num_symbols {
                match tm.get_transition(s, sym) {
                    Some(t) => {
                        match t.next_state {
                            State::Halt => {
                                reachable[s as usize] = true;
                                changed = true;
                                break;
                            }
                            State::Active(next_s) => {
                                if reachable[next_s as usize] {
                                    reachable[s as usize] = true;
                                    changed = true;
                                    break;
                                }
                            }
                        }
                    }
                    None => {
                        // Undefined transitions can be filled with a Halt transition
                        reachable[s as usize] = true;
                        changed = true;
                        break;
                    }
                }
            }
        }
    }

    reachable
}
