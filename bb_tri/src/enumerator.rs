use crate::simulator::{SimResult, Simulator};
use crate::tm::{Direction, State, Transition, TuringMachine};

use std::time::{Duration, Instant};
use std::sync::mpsc;
use rayon::prelude::*;

pub fn enumerate(
    num_states: u8, 
    num_symbols: u8, 
    step_limit: u64, 
    tx: mpsc::Sender<(TuringMachine, SimResult, Duration)>
) {
    let tm = TuringMachine::new(num_states, num_symbols);
    let sim = Simulator::new();
    let max_state = 0;
    let dirs_used = 0;
    let max_sym_written = 0;

    // Launch the recursion on the rayon thread pool so main thread can just recv()
    rayon::spawn(move || {
        enum_rec(tm, sim, step_limit, max_state, dirs_used, max_sym_written, Duration::ZERO, tx);
    });
}

fn enum_rec(
    tm: TuringMachine,
    mut sim: Simulator,
    step_limit: u64,
    max_state: u8,
    dirs_used: u8,
    max_sym_written: u8,
    accumulated_time: Duration,
    tx: mpsc::Sender<(TuringMachine, SimResult, Duration)>,
) {
    let start = Instant::now();
    let result = sim.run(&tm, step_limit);
    let elapsed = start.elapsed();
    let total_time = accumulated_time + elapsed;

    match result {
        SimResult::Halt(_, _) => {
            tx.send((tm, result, elapsed)).unwrap();
            return;
        }
        SimResult::LimitReached | SimResult::Infinite => {
            // We just report it back
            tx.send((tm, result, elapsed)).unwrap();
            return;
        }
        SimResult::UndefinedTrans => {
            let curr_state = match sim.state {
                State::Active(s) => s,
                State::Halt => unreachable!(),
            };
            let curr_symbol = sim.tape.nodes[sim.head as usize].symbol;
            
            let mut branches = Vec::new();

            // Canonical Halt branch: always 1RZ
            let mut halt_tm = tm.clone();
            halt_tm.set_transition(
                curr_state,
                curr_symbol,
                Transition {
                    symbol: 1,
                    dir: Direction::R,
                    next_state: State::Halt,
                },
            );
            let next_dirs_used_halt = std::cmp::max(dirs_used, 1);
            let next_sym_written_halt = std::cmp::max(max_sym_written, 1);
            branches.push((halt_tm, max_state, next_dirs_used_halt, next_sym_written_halt, accumulated_time));

            let max_sym = std::cmp::min(max_sym_written + 1, tm.num_symbols - 1);
            for sym in 0..=max_sym {
                let next_sym_written = std::cmp::max(max_sym_written, sym);
                let max_dir = std::cmp::min(dirs_used, 2);
                for dir_idx in 0..=max_dir {
                    let dir = match dir_idx {
                        0 => Direction::R,
                        1 => Direction::G,
                        2 => Direction::B,
                        _ => unreachable!(),
                    };
                    let next_dirs_used = std::cmp::max(dirs_used, dir_idx + 1);

                    // Possible Active next states
                    let max_next_state = std::cmp::min(max_state + 1, tm.num_states - 1);
                    for next_state_idx in 0..=max_next_state {
                        let mut new_tm = tm.clone();
                        new_tm.set_transition(
                            curr_state,
                            curr_symbol,
                            Transition {
                                symbol: sym,
                                dir,
                                next_state: State::Active(next_state_idx),
                            },
                        );
                        let next_max_state = std::cmp::max(max_state, next_state_idx);
                        
                        branches.push((new_tm, next_max_state, next_dirs_used, next_sym_written, total_time));
                    }
                }
            }

            branches.into_par_iter().for_each_with(tx, |tx_ref, (new_tm, next_max_state, next_dirs_used, next_sym_written, time)| {
                enum_rec(
                    new_tm,
                    sim.clone(),
                    step_limit,
                    next_max_state,
                    next_dirs_used,
                    next_sym_written,
                    time,
                    tx_ref.clone(),
                );
            });
        }
    }
}
