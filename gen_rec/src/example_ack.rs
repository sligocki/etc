/// A hand-built GRF encoding of a function with Ackermann growth.
use crate::grf::Grf;

// List <-> Integer encoding:
//    We encode a list of Nat into a Nat by using run lengths of 1s in binary encoding.
//    Ex: [1,2,3] -> 0b10110111 = 183

/// Pred(x) := x ∸ 1
/// R(Z0, P(2,1))
/// Arity: 1, Size: 3
pub fn pred() -> Grf {
    Grf::Rec(Box::new(Grf::Zero(0)), Box::new(Grf::Proj(2, 1)))
}

/// Not(x) := 1 if x = 0, else 0
/// R(C(S, Z0), Z2)
/// Arity: 1, Size: 5
pub fn not() -> Grf {
    Grf::Rec(
        Box::new(Grf::comp(Grf::Succ, vec![Grf::Zero(0)])),
        Box::new(Grf::Zero(2)),
    )
}

/// Sgn(x) := 0 if x = 0, else 1
/// R(Z0, C(S, Z2))
/// Arity: 1, Size: 5
pub fn sgn() -> Grf {
    Grf::Rec(
        Box::new(Grf::Zero(0)),
        Box::new(Grf::comp(Grf::Succ, vec![Grf::Zero(2)])),
    )
}

/// Plus2(x) := x + 2
/// C(S, S)
/// Arity: 1, Size: 3
pub fn plus2() -> Grf {
    Grf::comp(Grf::Succ, vec![Grf::Succ])
}

/// Double(x) := 2x
/// R(Z0, C(Plus2, P(2,2)))
/// Arity: 1, Size: 7
pub fn double() -> Grf {
    Grf::Rec(
        Box::new(Grf::Zero(0)),
        Box::new(Grf::comp(plus2(), vec![Grf::Proj(2, 2)])),
    )
}

/// RMonus(x,y) := y ∸ x
/// R(P(1,1), C(Pred, P(3,2)))
/// Arity: 2, Size: 7
pub fn rmonus() -> Grf {
    Grf::Rec(
        Box::new(Grf::Proj(1, 1)),
        Box::new(Grf::comp(pred(), vec![Grf::Proj(3, 2)])),
    )
}

/// Mod2(x) := x mod 2
/// R(Z0, C(Not, P(2,2)))
/// Arity: 1, Size: 9
pub fn mod2() -> Grf {
    Grf::Rec(
        Box::new(Grf::Zero(0)),
        Box::new(Grf::comp(not(), vec![Grf::Proj(2, 2)])),
    )
}

/// Shift(k,x) := x · 2^k
/// R(P(1,1), C(Double, P(3,2)))
/// Arity: 2, Size: 11
pub fn shift() -> Grf {
    Grf::Rec(
        Box::new(Grf::Proj(1, 1)),
        Box::new(Grf::comp(double(), vec![Grf::Proj(3, 2)])),
    )
}

/// RMonusOdd(x,y) := y ∸ (2x + 1)
/// R(Pred, C(Pred, C(Pred, P(3,2))))
/// Arity: 2, Size: 13
pub fn rmonus_odd() -> Grf {
    Grf::Rec(
        Box::new(pred()),
        Box::new(Grf::comp(pred(), vec![Grf::comp(pred(), vec![Grf::Proj(3, 2)])])),
    )
}

/// Div2(x) := ⌊x / 2⌋
/// M(RMonusOdd)
/// Arity: 1, Size: 14
pub fn div2() -> Grf {
    Grf::Min(Box::new(rmonus_odd()))
}

/// Div2k(k,x) := ⌊x / 2^k⌋
/// R(P(1,1), C(Div2, P(3,2)))
/// Arity: 2, Size: 18
pub fn div2k() -> Grf {
    Grf::Rec(
        Box::new(Grf::Proj(1, 1)),
        Box::new(Grf::comp(div2(), vec![Grf::Proj(3, 2)])),
    )
}

/// SafeBlock(k,x) := x · 2^k ∸ Sgn(k)
///   If k ≥ 1: Append (k-1) to list x
///   if k = 0: Do nothing
/// C(RMonus, C(Sgn, P(2,1)), Shift)
/// Arity: 2, Size: 26
pub fn safe_block() -> Grf {
    Grf::comp(
        rmonus(),
        vec![
            Grf::comp(sgn(), vec![Grf::Proj(2, 1)]),
            shift(),
        ],
    )
}

/// Bit(k,x) := the k-th bit of x
/// C(Mod2, Div2k)
/// Arity: 2, Size: 28
pub fn bit() -> Grf {
    Grf::comp(mod2(), vec![div2k()])
}

/// PopK(x) := Last value in list x (0 for empty list)
///   Length of the lowest run of 1-bits  (= min k s.t. bit k of x = 0)
/// M(Bit)
/// Arity: 1, Size: 29
pub fn pop_k() -> Grf {
    Grf::Min(Box::new(bit()))
}

/// AppendN(n, k, x): Append [k-1]*n to list x
/// R(P(2,2), C(SafeBlock, P(4,2), P(4,3)))
/// Arity: 3, Size: 31
pub fn append_n() -> Grf {
    Grf::Rec(
        Box::new(Grf::Proj(2, 2)),
        Box::new(Grf::comp(
            safe_block(),
            vec![Grf::Proj(4, 2), Grf::Proj(4, 3)],
        )),
    )
}

/// AckStep(n, x): Apply one step of Ackermann worm to list x
///   Equivalent to:
///     * Pop last element of list x -> k
///     * Append n+1 copies of k-1 to list x
/// C(Div2, C(AppendN, P(2,1), P(2,2), C(PopK, P(2,2))))
/// Arity: 2, Size: 80
pub fn ack_step() -> Grf {
    Grf::comp(
        div2(),
        vec![Grf::comp(
            append_n(),
            vec![
                Grf::Proj(2, 1),
                Grf::Proj(2, 2),
                Grf::comp(pop_k(), vec![Grf::Proj(2, 2)]),
            ],
        )],
    )
}

/// AckLoop(m, x): Iterate AckStep m times on list x (with increasing values of n)
///   It is known that for large enough m this will lead to x -> [] = 0
/// R(P(1,1), C(AckStep, P(3,1), P(3,2)))
/// Arity: 2, Size: 85
pub fn ack_loop() -> Grf {
    Grf::Rec(
        Box::new(Grf::Proj(1, 1)),
        Box::new(Grf::comp(
            ack_step(),
            vec![Grf::Proj(3, 1), Grf::Proj(3, 2)],
        )),
    )
}

/// AckWorm(x): A version of Hydra game/Goodstein sequence
///   Returns smallest m such that AckLoop(m, x) = []
/// Arity: 1, Size: 86
pub fn ack_worm() -> Grf {
    Grf::Min(Box::new(ack_loop()))
}

// TODO
// /// ack(n) dominates any PRF
// /// Arity: 0, Size: 
// pub fn ack() -> Grf {
//     Grf::comp(ack_worm(), )
// }

// pub fn rep_ack() -> Grf {

// }

// /// A GRF that computes a number > Graham's number
// /// Arity: 0, Size: ?
// pub fn graham() -> Grf {

// }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulate::{simulate, Num};

    fn eval(grf: &Grf, args: &[Num]) -> Option<Num> {
        let (result, _steps) = simulate(grf, args, 10_000_000);
        result.into_value()
    }

    // ── arity & size ───────────────────────────────────────────────────────────

    #[test]
    fn test_arity_and_size() {
        let cases: &[(&str, &dyn Fn() -> Grf, usize, usize)] = &[
            ("pred",       &pred,       1,  3),
            ("not",        &not,        1,  5),
            ("sgn",        &sgn,        1,  5),
            ("plus2",      &plus2,      1,  3),
            ("double",     &double,     1,  7),
            ("rmonus",     &rmonus,     2,  7),
            ("mod2",       &mod2,       1,  9),
            ("shift",      &shift,      2, 11),
            ("rmonus_odd", &rmonus_odd, 2, 13),
            ("div2",       &div2,       1, 14),
            ("div2k",      &div2k,      2, 18),
            ("safe_block", &safe_block, 2, 26),
            ("bit",        &bit,        2, 28),
            ("pop_k",      &pop_k,      1, 29),
            ("append_n",   &append_n,   3, 31),
            ("ack_step",   &ack_step,   2, 80),
            ("ack_loop", &ack_loop, 2, 85),
            ("ack_worm",   &ack_worm,   1, 86),
        ];
        for (name, f, arity, size) in cases {
            let g = f();
            assert_eq!(g.arity(), *arity, "{name}: wrong arity");
            assert_eq!(g.size(),  *size,  "{name}: wrong size");
        }
    }

    // ── mathematical spec ──────────────────────────────────────────────────────

    #[test]
    fn test_pred() {
        let f = pred();
        assert_eq!(eval(&f, &[0]), Some(0)); // 0 ∸ 1 = 0
        assert_eq!(eval(&f, &[1]), Some(0));
        assert_eq!(eval(&f, &[5]), Some(4));
    }

    #[test]
    fn test_not() {
        let f = not();
        assert_eq!(eval(&f, &[0]), Some(1));
        assert_eq!(eval(&f, &[1]), Some(0));
        assert_eq!(eval(&f, &[5]), Some(0));
    }

    #[test]
    fn test_sgn() {
        let f = sgn();
        assert_eq!(eval(&f, &[0]), Some(0));
        assert_eq!(eval(&f, &[1]), Some(1));
        assert_eq!(eval(&f, &[5]), Some(1));
    }

    #[test]
    fn test_plus2() {
        let f = plus2();
        assert_eq!(eval(&f, &[0]), Some(2));
        assert_eq!(eval(&f, &[3]), Some(5));
    }

    #[test]
    fn test_double() {
        let f = double();
        for x in 0u64..10 {
            assert_eq!(eval(&f, &[x]), Some(2 * x), "double({x})");
        }
    }

    #[test]
    fn test_rmonus() {
        // rmonus(x, y) = y ∸ x
        let f = rmonus();
        assert_eq!(eval(&f, &[0, 5]), Some(5));
        assert_eq!(eval(&f, &[3, 5]), Some(2));
        assert_eq!(eval(&f, &[5, 3]), Some(0)); // truncated: 3 ∸ 5 = 0
        assert_eq!(eval(&f, &[5, 5]), Some(0));
    }

    #[test]
    fn test_mod2() {
        let f = mod2();
        for x in 0u64..10 {
            assert_eq!(eval(&f, &[x]), Some(x % 2), "mod2({x})");
        }
    }

    #[test]
    fn test_shift() {
        // shift(k, x) = x * 2^k
        let f = shift();
        assert_eq!(eval(&f, &[0, 5]), Some(5));
        assert_eq!(eval(&f, &[1, 5]), Some(10));
        assert_eq!(eval(&f, &[3, 1]), Some(8));
        assert_eq!(eval(&f, &[4, 3]), Some(48));
    }

    #[test]
    fn test_rmonus_odd() {
        // rmonus_odd(x, y) = y ∸ (2x + 1)
        let f = rmonus_odd();
        assert_eq!(eval(&f, &[0, 5]), Some(4)); // 5 ∸ 1 = 4
        assert_eq!(eval(&f, &[1, 5]), Some(2)); // 5 ∸ 3 = 2
        assert_eq!(eval(&f, &[2, 5]), Some(0)); // 5 ∸ 5 = 0
        assert_eq!(eval(&f, &[3, 5]), Some(0)); // 5 ∸ 7 = 0
    }

    #[test]
    fn test_div2() {
        let f = div2();
        for x in 0u64..=12 {
            assert_eq!(eval(&f, &[x]), Some(x / 2), "div2({x})");
        }
    }

    #[test]
    fn test_div2k() {
        // div2k(k, x) = ⌊x / 2^k⌋
        let f = div2k();
        assert_eq!(eval(&f, &[0, 8]), Some(8));
        assert_eq!(eval(&f, &[1, 8]), Some(4));
        assert_eq!(eval(&f, &[2, 8]), Some(2));
        assert_eq!(eval(&f, &[3, 8]), Some(1));
        assert_eq!(eval(&f, &[4, 8]), Some(0));
        for k in 0u64..=5 {
            for x in 0u64..=20 {
                assert_eq!(
                    eval(&f, &[k, x]),
                    Some(x / 2u64.pow(k as u32)),
                    "div2k({k}, {x})"
                );
            }
        }
    }

    #[test]
    fn test_safe_block() {
        // safe_block(k, x) = x * 2^k ∸ Sgn(k)
        let f = safe_block();
        assert_eq!(eval(&f, &[0, 3]), Some(3));  // 3*1 ∸ 0 = 3
        assert_eq!(eval(&f, &[1, 3]), Some(5));  // 3*2 ∸ 1 = 5
        assert_eq!(eval(&f, &[2, 3]), Some(11)); // 3*4 ∸ 1 = 11
        assert_eq!(eval(&f, &[3, 1]), Some(7));  // 1*8 ∸ 1 = 7
        assert_eq!(eval(&f, &[0, 0]), Some(0));  // 0*1 ∸ 0 = 0
        assert_eq!(eval(&f, &[1, 0]), Some(0));  // 0*2 ∸ 1 = 0 (truncated)
    }

    #[test]
    fn test_bit() {
        // bit(k, x) = the k-th bit of x
        let f = bit();
        // 5 = 0b101
        assert_eq!(eval(&f, &[0, 5]), Some(1));
        assert_eq!(eval(&f, &[1, 5]), Some(0));
        assert_eq!(eval(&f, &[2, 5]), Some(1));
        assert_eq!(eval(&f, &[3, 5]), Some(0));
        // exhaustive check for small values
        for x in 0u64..=15 {
            for k in 0u64..=5 {
                assert_eq!(
                    eval(&f, &[k, x]),
                    Some((x >> k) & 1),
                    "bit({k}, {x})"
                );
            }
        }
    }

    #[test]
    fn test_pop_k() {
        // pop_k(x) = number of trailing 1-bits (length of lowest 1-run)
        let f = pop_k();
        assert_eq!(eval(&f, &[0b0]),  Some(0));
        assert_eq!(eval(&f, &[0b1]),  Some(1));
        assert_eq!(eval(&f, &[0b10]),  Some(0));
        assert_eq!(eval(&f, &[0b11]),  Some(2));
        assert_eq!(eval(&f, &[0b110]),  Some(0));
        assert_eq!(eval(&f, &[0b111]),  Some(3));
        assert_eq!(eval(&f, &[0b1111]), Some(4));
        assert_eq!(eval(&f, &[0b11011]), Some(2));
        assert_eq!(eval(&f, &[0b11001]), Some(1));
        assert_eq!(eval(&f, &[0b10100]), Some(0));
    }

    #[test]
    fn test_append_n() {
        // append_n(n, k, x):
        //   base:  append_n(0, k, x) = x   [P(2,2) selects x as 2nd rest-arg]
        //   step:  append_n(n+1, k, x) = safe_block(append_n(n,k,x), k)
        //            where safe_block(a, b) = b * 2^a ∸ Sgn(a)
        let f = append_n();
        // Base cases (n = 0): result = x unchanged
        assert_eq!(eval(&f, &[0, 0, 0]), Some(0));
        assert_eq!(eval(&f, &[0, 2, 3]), Some(3));
        assert_eq!(eval(&f, &[0, 1, 7]), Some(7));
        // One step: safe_block(x, k) = k * 2^x ∸ Sgn(x)
        // append_n(1, 1, 3): safe_block(3, 1) = 1*8 ∸ 1 = 7
        assert_eq!(eval(&f, &[1, 1, 3]), Some(7));
        // append_n(1, 2, 3): safe_block(3, 2) = 2*8 ∸ 1 = 15
        assert_eq!(eval(&f, &[1, 2, 3]), Some(15));
        // Two steps: safe_block(safe_block(x, k), k)
        // append_n(2, 1, 3): safe_block(7, 1) = 1*128 ∸ 1 = 127
        assert_eq!(eval(&f, &[2, 1, 3]), Some(127));
    }

    #[test]
    fn test_ack_step() {
        // ack_step(a, b) = Div2(append_n(a, b, PopK(b)))
        let f = ack_step();
        // a=0: Div2(PopK(b))
        assert_eq!(eval(&f, &[0, 1]),  Some(0)); // PopK(1)=1, Div2(1)=0
        assert_eq!(eval(&f, &[0, 3]),  Some(1)); // PopK(3)=2, Div2(2)=1
        assert_eq!(eval(&f, &[0, 7]),  Some(1)); // PopK(7)=3, Div2(3)=1
        assert_eq!(eval(&f, &[0, 15]), Some(2)); // PopK(15)=4, Div2(4)=2
        // a=1, b=1: append_n(1,1,1)=safe_block(PopK(1),1)=safe_block(1,1)=1*2∸1=1; Div2(1)=0
        assert_eq!(eval(&f, &[1, 1]),  Some(0));
    }

    #[test]
    fn test_ack_loop() {
        // ack_loop(0, x) = x
        // ack_loop(n+1, x) = ack_step(n, ack_loop(n, x))
        let f = ack_loop();
        for x in 0u64..=5 {
            assert_eq!(eval(&f, &[0, x]), Some(x));
        }
        assert_eq!(eval(&f, &[1, 3]),  Some(1)); // ack_step(0,3)=1
        assert_eq!(eval(&f, &[2, 3]),  Some(0)); // ack_step(1,1)=0
    }

    #[test]
    fn test_ack_worm_small() {
        // ack_worm(x) = min{n : ack_loop(n,x) = 0}
        let f = ack_worm();
        assert_eq!(eval(&f, &[0]),  Some(0)); // StateLoop(0,0)=0 immediately
        assert_eq!(eval(&f, &[1]),  Some(1)); // StateLoop(1,1)=ack_step(0,1)=0
        assert_eq!(eval(&f, &[2]),  Some(1)); // StateLoop(1,2)=ack_step(0,2)=0
        assert_eq!(eval(&f, &[3]),  Some(2)); // terminates at step 2
        assert_eq!(eval(&f, &[7]),  Some(2)); // terminates at step 2
        assert_eq!(eval(&f, &[15]), Some(3)); // terminates at step 3
    }
}
