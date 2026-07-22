use crate::tag_system::TagSystem;

#[derive(Debug, Clone)]
pub enum InfiniteReason {
    Cycle(usize), // period
    ImmortalSubstring(Vec<u8>),
    NonDecreasingSymbol(u8),
    ClosedSymbol(u8),
    TranslationCycle(usize, Vec<u8>), // period, appended suffix
}

#[derive(Debug, Clone)]
pub enum HaltCondition {
    Halted(usize, usize), // steps, max_length
    Infinite(InfiniteReason, usize), // reason, steps taken to detect
    Unknown,
    UndefinedRule(u8),
}

#[derive(Clone)]
pub struct Simulator<'a> {
    pub sys: &'a TagSystem,
    pub tape: Vec<u8>,
    pub head_idx: usize,
    pub steps: usize,
    pub max_len: usize,
    pub saved_tape: Vec<u8>,
    pub power: usize,
    pub lam: usize,
    pub symbol_counts: Vec<usize>,
    pub non_decreasing: Vec<u8>,
    pub closed_symbols: Vec<u8>,
}

impl<'a> Simulator<'a> {
    pub fn new(sys: &'a TagSystem) -> Self {
        let tape = vec![0u8; sys.v];
        let mut saved_tape = Vec::with_capacity(64);
        saved_tape.extend_from_slice(&tape);
        
        let mut symbol_counts = vec![0; 256];
        for &c in &tape {
            symbol_counts[c as usize] += 1;
        }
        
        let non_decreasing = sys.non_decreasing_symbols();
        let closed_symbols = sys.closed_symbols();

        Simulator {
            sys,
            tape,
            head_idx: 0,
            steps: 0,
            max_len: sys.v,
            saved_tape,
            power: 1,
            lam: 0,
            symbol_counts,
            non_decreasing,
            closed_symbols,
        }
    }

    pub fn step(&mut self, verbose: bool) -> Option<HaltCondition> {
        if self.steps == 0 && self.closed_symbols.contains(&0) {
            if verbose {
                println!("Symbol 0 is closed (only outputs 0 at read heads) and initial tape only has 0 at read heads!");
            }
            return Some(HaltCondition::Infinite(InfiniteReason::ClosedSymbol(0), 0));
        }
        for &c in &self.non_decreasing {
            if self.symbol_counts[c as usize] >= self.sys.v {
                if verbose {
                    println!("Number of symbol {} reached {} (>= {}), will never decrease!", c, self.symbol_counts[c as usize], self.sys.v);
                }
                return Some(HaltCondition::Infinite(InfiniteReason::NonDecreasingSymbol(c), self.steps));
            }
        }

        if verbose {
            print!("Step {}: Tape ", self.steps);
            for i in self.head_idx..self.tape.len() {
                print!("{}", self.tape[i]);
            }
            println!();
        }

        self.steps += 1;
        self.lam += 1;
        
        let head = self.tape[self.head_idx];
        let start = self.head_idx;
        self.head_idx += self.sys.v;
        for i in start..self.head_idx {
            let c = self.tape[i];
            self.symbol_counts[c as usize] -= 1;
        }

        let rule = match &self.sys.rules[head as usize] {
            Some(r) => r,
            None => return Some(HaltCondition::UndefinedRule(head)),
        };

        for &c in rule {
            self.tape.push(c);
            self.symbol_counts[c as usize] += 1;
        }

        let current_len = self.tape.len() - self.head_idx;
        if current_len > self.max_len {
            self.max_len = current_len;
        }

        if current_len == self.saved_tape.len() && self.tape[self.head_idx..] == self.saved_tape[..] {
            if verbose {
                println!("Exact cycle of period {} detected!", self.lam);
            }
            return Some(HaltCondition::Infinite(InfiniteReason::Cycle(self.lam), self.steps));
        }

        if self.lam == self.power {
            self.power *= 2;
            self.lam = 0;
            if current_len < 10_000 {
                self.saved_tape.clear();
                self.saved_tape.extend_from_slice(&self.tape[self.head_idx..]);
            }
        }

        if self.head_idx > 1_000_000 {
            self.tape.drain(0..self.head_idx);
            self.head_idx = 0;
        }

        None
    }

    pub fn run(&mut self, max_steps: usize, verbose: bool) -> HaltCondition {
        while self.tape.len() - self.head_idx >= self.sys.v {
            if self.steps >= max_steps {
                return HaltCondition::Unknown;
            }
            if let Some(cond) = self.step(verbose) {
                return cond;
            }
        }
        
        if verbose {
            print!("Step {}: Tape ", self.steps);
            if self.tape.len() == self.head_idx {
                println!("eps");
            } else {
                for i in self.head_idx..self.tape.len() {
                    print!("{}", self.tape[i]);
                }
                println!();
            }
        }

        HaltCondition::Halted(self.steps, self.max_len)
    }
}

pub fn simulate(sys: &TagSystem, max_steps: usize, verbose: bool) -> HaltCondition {
    Simulator::new(sys).run(max_steps, verbose)
}
