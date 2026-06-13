use crate::tm::{Direction, State, Transition, TuringMachine};

pub fn parse_tm(s: &str) -> Result<TuringMachine, String> {
    let states: Vec<&str> = s.split('_').collect();
    let num_states = states.len() as u8;
    
    // Determine number of symbols from the length of the first state string
    // Each transition is 3 characters (e.g. "1RB").
    if states.is_empty() || states[0].len() % 3 != 0 {
        return Err("Invalid transition format length".to_string());
    }
    let num_symbols = (states[0].len() / 3) as u8;

    let mut tm = TuringMachine::new(num_states, num_symbols);

    for (state_idx, state_str) in states.iter().enumerate() {
        if state_str.len() != (num_symbols as usize * 3) {
            return Err(format!("State {} has inconsistent number of symbols", state_idx));
        }

        for symbol_idx in 0..num_symbols {
            let start = (symbol_idx as usize) * 3;
            let trans_str = &state_str[start..start + 3];

            if trans_str == "---" {
                continue; // Undefined
            }

            let write_char = trans_str.chars().nth(0).unwrap();
            let dir_char = trans_str.chars().nth(1).unwrap();
            let next_state_char = trans_str.chars().nth(2).unwrap();

            let write_symbol = write_char.to_digit(10).ok_or("Invalid write symbol")? as u8;
            
            let dir = Direction::from_char(dir_char).ok_or("Invalid direction")?;
            
            let next_state = if next_state_char == 'Z' {
                State::Halt
            } else {
                let state_val = (next_state_char as u8).checked_sub(b'A').ok_or("Invalid state")?;
                if state_val >= num_states {
                    return Err(format!("State out of bounds: {}", next_state_char));
                }
                State::Active(state_val)
            };

            tm.set_transition(
                state_idx as u8,
                symbol_idx,
                Transition {
                    symbol: write_symbol,
                    dir,
                    next_state,
                },
            );
        }
    }

    Ok(tm)
}

pub fn tm_to_string(tm: &TuringMachine) -> String {
    let mut s = String::new();
    for state in 0..tm.num_states {
        if state > 0 {
            s.push('_');
        }
        for symbol in 0..tm.num_symbols {
            if let Some(trans) = tm.get_transition(state, symbol) {
                s.push_str(&trans.symbol.to_string());
                s.push(trans.dir.to_char());
                match trans.next_state {
                    State::Halt => s.push('Z'),
                    State::Active(st) => s.push((b'A' + st) as char),
                }
            } else {
                s.push_str("---");
            }
        }
    }
    s
}
