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
pub enum UnknownReason {
    OverSteps,
    OverSize,
}

#[derive(Debug, Clone)]
pub enum HaltCondition {
    Halted(usize, usize),            // steps, max_length
    Infinite(InfiniteReason, usize), // reason, steps taken to detect
    Unknown(UnknownReason, usize),   // reason, steps taken to abort
    UndefinedRule(u8),
}

#[derive(Clone)]
pub struct Simulator<'a> {
    pub sys: &'a TagSystem,
    pub tape: Vec<u8>, // Active tape
    pub head_idx: usize,
    pub steps: usize,
    pub true_length: usize, // Current space
    pub max_len: usize, // Max true_length
    pub saved_tape: Vec<u8>,
    pub saved_phase: usize,
    pub power: usize,
    pub lam: usize,
    pub symbol_counts: Vec<usize>,
    pub non_decreasing: Vec<u8>,
    pub closed_symbols: Vec<u8>,
    pub splits: Vec<Vec<Option<Vec<u8>>>>, // [symbol][phase]
}

impl<'a> Simulator<'a> {
    pub fn new(sys: &'a TagSystem) -> Self {
        let tape = vec![0u8];
        let mut saved_tape = Vec::with_capacity(64);
        saved_tape.extend_from_slice(&tape);

        let mut symbol_counts = vec![0; 256];
        symbol_counts[0] = 1;

        let mut splits = vec![vec![None; sys.v]; sys.rules.len()];
        for (c, rule_opt) in sys.rules.iter().enumerate() {
            if let Some(rule) = rule_opt {
                for phase in 0..sys.v {
                    let mut split = Vec::new();
                    for (i, &sym) in rule.iter().enumerate() {
                        if (phase + i) % sys.v == 0 {
                            split.push(sym);
                        }
                    }
                    splits[c][phase] = Some(split);
                }
            }
        }

        let mut non_decreasing = Vec::new();

        let mut closed_symbols = Vec::new();
        for c in 0..sys.rules.len() {
            if let Some(rule) = &sys.rules[c] {
                if rule.len() >= sys.v && rule.len() % sys.v == 0 {
                    let mut all_match = true;
                    for i in (0..rule.len()).step_by(sys.v) {
                        if rule[i] != c as u8 {
                            all_match = false;
                            break;
                        }
                    }
                    if all_match {
                        closed_symbols.push(c as u8);
                    }
                }
            }
        }

        Simulator {
            sys,
            tape,
            head_idx: 0,
            steps: 0,
            true_length: sys.v,
            max_len: sys.v,
            saved_tape,
            saved_phase: sys.v % sys.v,
            power: 1,
            lam: 0,
            symbol_counts,
            non_decreasing,
            closed_symbols,
            splits,
        }
    }

    pub fn step(&mut self, verbose: bool, use_deciders: bool) -> Option<HaltCondition> {
        if use_deciders {
            if self.steps == 0 {
                if self.closed_symbols.contains(&0) {
                    if verbose {
                        println!("Symbol 0 is closed and initial tape only has 0!");
                    }
                    return Some(HaltCondition::Infinite(InfiniteReason::ClosedSymbol(0), 0));
                }
                if self.sys.non_decreasing_symbols().contains(&0) {
                    if verbose {
                        println!("Symbol 0 is non-decreasing and initial tape has {} copies!", self.sys.v);
                    }
                    return Some(HaltCondition::Infinite(InfiniteReason::NonDecreasingSymbol(0), 0));
                }
            }
        }

        if verbose {
            print!("Step {}: ActiveTape ", self.steps);
            for i in self.head_idx..self.tape.len() {
                print!("{}", self.tape[i]);
            }
            println!(" (phase {})", self.true_length % self.sys.v);
        }

        self.steps += 1;
        self.lam += 1;

        let head = self.tape[self.head_idx];
        self.head_idx += 1; // Active tape consumes 1 symbol
        self.symbol_counts[head as usize] -= 1;

        let phase = self.true_length % self.sys.v;
        let rule_split = match &self.splits[head as usize][phase] {
            Some(r) => r,
            None => return Some(HaltCondition::UndefinedRule(head)),
        };
        let raw_rule = self.sys.rules[head as usize].as_ref().unwrap();

        for &c in rule_split {
            self.tape.push(c);
            self.symbol_counts[c as usize] += 1;
        }

        self.true_length = self.true_length + raw_rule.len() - self.sys.v;
        
        let current_len = self.tape.len() - self.head_idx;
        if self.true_length > self.max_len {
            self.max_len = self.true_length;
        }

        if use_deciders {
            let next_phase = self.true_length % self.sys.v;
            if current_len == self.saved_tape.len() 
                && self.tape[self.head_idx..] == self.saved_tape[..]
                && next_phase == self.saved_phase
            {
                if verbose {
                    println!("Exact cycle of period {} detected!", self.lam);
                }
                return Some(HaltCondition::Infinite(
                    InfiniteReason::Cycle(self.lam),
                    self.steps,
                ));
            }

            if self.lam == self.power {
                self.power *= 2;
                self.lam = 0;
                if current_len < 10_000 {
                    self.saved_tape.clear();
                    self.saved_tape
                        .extend_from_slice(&self.tape[self.head_idx..]);
                    self.saved_phase = next_phase;
                }
            }
        }

        if self.head_idx > 1_000_000 {
            self.tape.drain(0..self.head_idx);
            self.head_idx = 0;
        }

        None
    }

    pub fn run(&mut self, max_steps: usize, max_space: usize, verbose: bool, use_deciders: bool) -> HaltCondition {
        while self.true_length >= self.sys.v {
            if self.steps >= max_steps {
                return HaltCondition::Unknown(UnknownReason::OverSteps, self.steps);
            }
            if self.tape.len() - self.head_idx > max_space {
                return HaltCondition::Unknown(UnknownReason::OverSize, self.steps);
            }
            if let Some(cond) = self.step(verbose, use_deciders) {
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

pub fn simulate(sys: &TagSystem, max_steps: usize, max_space: usize, verbose: bool, use_deciders: bool) -> HaltCondition {
    Simulator::new(sys).run(max_steps, max_space, verbose, use_deciders)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tag_system::TagSystem;

    fn run_sim(s: &str) -> HaltCondition {
        let sys = TagSystem::parse(2, s);
        let mut sim = Simulator::new(&sys);
        sim.run(10_000, 1_000_000, false, true)
    }

    #[test]
    fn test_halt() {
        match run_sim("100_") {
            HaltCondition::Halted(steps, space) => {
                assert_eq!(steps, 2);
                assert_eq!(space, 3);
            }
            other => panic!("Expected Halted, got {:?}", other),
        }
    }

    #[test]
    fn test_cycle() {
        match run_sim("001_") {
            HaltCondition::Infinite(InfiniteReason::Cycle(p), _) => assert_eq!(p, 3),
            other => panic!("Expected Cycle(3), got {:?}", other),
        }
    }

    #[test]
    fn test_non_decreasing() {
        match run_sim("010_0") {
            HaltCondition::Infinite(InfiniteReason::NonDecreasingSymbol(0), _) => {}
            other => panic!("Expected NonDecreasingSymbol(0), got {:?}", other),
        }
    }

    #[test]
    fn test_closed_symbol() {
        match run_sim("01_?") {
            HaltCondition::Infinite(InfiniteReason::ClosedSymbol(0), _) => {}
            other => panic!("Expected ClosedSymbol(0), got {:?}", other),
        }
    }

    #[test]
    fn test_champions_halting() {
        // S=6
        match run_sim("011_1") {
            HaltCondition::Halted(steps, _) => assert_eq!(steps, 5),
            other => panic!("Expected Halted, got {:?}", other),
        }
        
        // S=7
        match run_sim("0111_1") {
            HaltCondition::Halted(steps, _) => assert_eq!(steps, 10),
            other => panic!("Expected Halted, got {:?}", other),
        }
        
        // S=8
        match run_sim("111_20_") {
            HaltCondition::Halted(steps, _) => assert_eq!(steps, 19),
            other => panic!("Expected Halted, got {:?}", other),
        }
        
        // S=9
        match run_sim("11_021_2") {
            HaltCondition::Halted(steps, _) => assert_eq!(steps, 49),
            other => panic!("Expected Halted, got {:?}", other),
        }
        
        // S=10
        match run_sim("112_1_002") {
            HaltCondition::Halted(steps, _) => assert_eq!(steps, 779),
            other => panic!("Expected Halted, got {:?}", other),
        }
        
        // S=11
        // (Use a larger step limit just in case, though 196841 is within the 10M default of run_sim? 
        // Wait, run_sim uses 10_000! Let's pass a larger limit for this one)
        let sys11 = TagSystem::parse(2, "120221_0_2");
        match simulate(&sys11, 200_000, 1_000_000, false, true) {
            HaltCondition::Halted(steps, _) => assert_eq!(steps, 196841),
            other => panic!("Expected Halted, got {:?}", other),
        }
    }
}
