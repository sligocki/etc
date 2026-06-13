use crate::simulator::{SimResult, Simulator};
use crate::tm::{Direction, State, Transition, TuringMachine};

use std::time::{Duration, Instant};

pub fn enumerate<F>(num_states: u8, num_symbols: u8, step_limit: u64, mut on_tm: F)
where
    F: FnMut(&TuringMachine, &SimResult, Duration),
{
    let tm = TuringMachine::new(num_states, num_symbols);
    let sim = Simulator::new();
    let max_state = 0;
    let dirs_used = 0;

    enum_rec(tm, sim, step_limit, max_state, dirs_used, Duration::ZERO, &mut on_tm);
}

fn enum_rec<F>(
    tm: TuringMachine,
    mut sim: Simulator,
    step_limit: u64,
    max_state: u8,
    dirs_used: u8,
    accumulated_time: Duration,
    on_tm: &mut F,
) where
    F: FnMut(&TuringMachine, &SimResult, Duration),
{
    let start = Instant::now();
    let result = sim.run(&tm, step_limit);
    let elapsed = start.elapsed();
    let total_time = accumulated_time + elapsed;

    match result {
        SimResult::Halt(_, _) | SimResult::LimitReached => {
            on_tm(&tm, &result, total_time);
        }
        SimResult::UndefinedTrans => {
            let curr_state = match sim.state {
                State::Active(s) => s,
                State::Halt => unreachable!(),
            };
            let curr_symbol = sim.tape.read(&sim.head);

            for sym in 0..tm.num_symbols {
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
                        enum_rec(
                            new_tm,
                            sim.clone(),
                            step_limit,
                            next_max_state,
                            next_dirs_used,
                            total_time,
                            on_tm,
                        );
                    }

                    // Halt state
                    let mut new_tm = tm.clone();
                    new_tm.set_transition(
                        curr_state,
                        curr_symbol,
                        Transition {
                            symbol: sym,
                            dir,
                            next_state: State::Halt,
                        },
                    );
                    enum_rec(
                        new_tm,
                        sim.clone(),
                        step_limit,
                        max_state,
                        next_dirs_used,
                        total_time,
                        on_tm,
                    );
                }
            }
        }
    }
}
