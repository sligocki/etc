#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum State {
    Halt,
    Active(u8), // 0 = A, 1 = B, etc.
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Direction {
    R,
    G,
    B,
}

impl Direction {
    pub fn to_char(self) -> char {
        match self {
            Direction::R => 'R',
            Direction::G => 'G',
            Direction::B => 'B',
        }
    }

    pub fn from_char(c: char) -> Option<Self> {
        match c {
            'R' => Some(Direction::R),
            'G' => Some(Direction::G),
            'B' => Some(Direction::B),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Transition {
    pub symbol: u8,
    pub dir: Direction,
    pub next_state: State,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TuringMachine {
    pub num_states: u8,
    pub num_symbols: u8,
    // transitions[state as usize][symbol as usize]
    // None means the transition is undefined (used for enumeration)
    pub transitions: Vec<Vec<Option<Transition>>>,
}

impl TuringMachine {
    pub fn new(num_states: u8, num_symbols: u8) -> Self {
        let mut transitions = Vec::with_capacity(num_states as usize);
        for _ in 0..num_states {
            let mut state_trans = Vec::with_capacity(num_symbols as usize);
            for _ in 0..num_symbols {
                state_trans.push(None);
            }
            transitions.push(state_trans);
        }
        Self {
            num_states,
            num_symbols,
            transitions,
        }
    }

    pub fn get_transition(&self, state: u8, symbol: u8) -> Option<Transition> {
        self.transitions[state as usize][symbol as usize]
    }

    pub fn set_transition(&mut self, state: u8, symbol: u8, transition: Transition) {
        self.transitions[state as usize][symbol as usize] = Some(transition);
    }
}
