/// A hand-built GRF encoding of a function with Ackermann growth.
use crate::grf::Grf;
use crate::examples::{constant, rep_succ, diag_rep, diag_succ};

// List <-> Integer encoding:
//    We encode a list of Nat into a Nat by using run lengths of 1s in binary encoding.
//    Ex: [1,2,3] -> 0b10110111 = 183

/// Pred(x) := x ∸ 1
/// R(Z0, P(2,1))
/// Arity: 1, Size: 3
pub fn pred() -> Grf {
    Grf::rec(Grf::Zero(0), Grf::Proj(2, 1))
}

/// Not(x) := 1 if x = 0, else 0
/// R(C(S, Z0), Z2)
/// Arity: 1, Size: 5
pub fn not() -> Grf {
    Grf::rec(Grf::comp(Grf::Succ, vec![Grf::Zero(0)]), Grf::Zero(2))
}

/// Sgn(x) := 0 if x = 0, else 1
/// R(Z0, C(S, Z2))
/// Arity: 1, Size: 5
pub fn sgn() -> Grf {
    Grf::rec(Grf::Zero(0), Grf::comp(Grf::Succ, vec![Grf::Zero(2)]))
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
    Grf::rec(Grf::Zero(0), Grf::comp(plus2(), vec![Grf::Proj(2, 2)]))
}

/// RMonus(x,y) := y ∸ x
/// R(P(1,1), C(Pred, P(3,2)))
/// Arity: 2, Size: 7
pub fn rmonus() -> Grf {
    Grf::rec(Grf::Proj(1, 1), Grf::comp(pred(), vec![Grf::Proj(3, 2)]))
}

/// Mod2(x) := x mod 2
/// R(Z0, C(Not, P(2,2)))
/// Arity: 1, Size: 9
pub fn mod2() -> Grf {
    Grf::rec(Grf::Zero(0), Grf::comp(not(), vec![Grf::Proj(2, 2)]))
}

/// Shift(k,x) := x · 2^k
/// R(P(1,1), C(Double, P(3,2)))
/// Arity: 2, Size: 11
pub fn shift() -> Grf {
    Grf::rec(Grf::Proj(1, 1), Grf::comp(double(), vec![Grf::Proj(3, 2)]))
}

/// RMonusOdd(x,y) := y ∸ (2x + 1)
/// R(Pred, C(Pred, C(Pred, P(3,2))))
/// Arity: 2, Size: 13
pub fn rmonus_odd() -> Grf {
    Grf::rec(
        pred(),
        Grf::comp(pred(), vec![Grf::comp(pred(), vec![Grf::Proj(3, 2)])]),
    )
}

/// Div2(x) := ⌊x / 2⌋
/// M(RMonusOdd)
/// Arity: 1, Size: 14
pub fn div2() -> Grf {
    Grf::min(rmonus_odd())
}

/// Div2k(k,x) := ⌊x / 2^k⌋
/// R(P(1,1), C(Div2, P(3,2)))
/// Arity: 2, Size: 18
pub fn div2k() -> Grf {
    Grf::rec(Grf::Proj(1, 1), Grf::comp(div2(), vec![Grf::Proj(3, 2)]))
}

/// Append(k,x) := x · 2^k ∸ Sgn(k)
///   If k ≥ 1: Decrement last value of list x and append k ([..., a] -> [..., a-1, k])
///   if k = 0: Do nothing
/// C(RMonus, C(Sgn, P(2,1)), Shift)
/// Arity: 2, Size: 26
pub fn append() -> Grf {
    Grf::comp(
        rmonus(),
        vec![Grf::comp(sgn(), vec![Grf::Proj(2, 1)]), shift()],
    )
}

/// AppendN(n, k, x): [...] + [k] -> [...] + [k-1]*n + [k]
/// R(P(2,2), C(SafeBlock, P(4,3), P(4,2)))
/// Arity: 3, Size: 31
pub fn append_n() -> Grf {
    Grf::rec(
        Grf::Proj(2, 2),
        Grf::comp(append(), vec![Grf::Proj(4, 3), Grf::Proj(4, 2)]),
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
    Grf::min(bit())
}

/// AckStep(n, x): Apply one step of Ackermann worm to list x
///   Equivalent to:
///     * Pop last element of list x -> k
///     * Append n+1 copies of k-1 to list x
/// C(Div2, C(AppendN, P(2,1), C(PopK, P(2,2)), P(2,2)))
/// Arity: 2, Size: 80
pub fn ack_step() -> Grf {
    Grf::comp(
        div2(),
        vec![Grf::comp(
            append_n(),
            vec![
                Grf::Proj(2, 1), // n
                Grf::comp(pop_k(), vec![Grf::Proj(2, 2)]),
                Grf::Proj(2, 2), // x
            ],
        )],
    )
}

/// AckLoop(m, x): Iterate AckStep m times on list x (with increasing values of n)
///   It is known that for large enough m this will lead to x -> [] = 0
/// R(P(1,1), C(AckStep, P(3,1), P(3,2)))
/// Arity: 2, Size: 85
pub fn ack_loop() -> Grf {
    Grf::rec(
        Grf::Proj(1, 1),
        Grf::comp(ack_step(), vec![Grf::Proj(3, 1), Grf::Proj(3, 2)]),
    )
}

/// AckWorm(x): A version of Hydra game/Goodstein sequence
///     Equivalent to algorithm:
///         N = 0
///         while list x is not empty and not all 0s:
///             N += 1
///             k = pop_last(x)
///             if k > 0: append N copies of (k-1) to x
///         return N
///     Guaranteed to halt on all inputs, but it grows faster than all PRF
/// M(AckLoop)
/// Arity: 1, Size: 86
pub fn ack_worm() -> Grf {
    Grf::min(ack_loop())
}
// AckWorm([4]) = 41 2^38 - 1 = [1,1,0,0,38]

/// InitList(n,_) := list ending in a value >= n
pub fn init_list() -> Grf {
    // (n,m) -> (m+2) 2^n - 1
    // A number ending in at least n+1 1s in binary
    diag_rep(rep_succ(Grf::Succ))
}
// InitList(0,0) = 2 2^0 - 1 = 0b1 = [1]
// InitList(1,1) = 3 2^1 - 1 = 0b101 = [1,1]
// InitList(2,2) = 4 2^2 - 1 = 0b1111 = [4]
// InitList(3,3) = 5 2^3 - 1 = 0b100111 = [1,0,3]

/// Ack(n,_) > AckWorm([n+1])
///     Dominates all PRF
/// C(AckWorm, InitList)
pub fn ack() -> Grf {
    Grf::comp(ack_worm(), vec![init_list()])
}
// Ack(1) = AckWomr([1,1]) = 3
// Ack(2) = AckWorm([4]) = 41 2^38 - 1
// Ack(3) = AckWorm([1,0,3]) = 16

/// Omega() > f_omega(10^10)
pub fn omega() -> Grf {
    // f(n,n) = ack^n(n)
    let ack_diag = Grf::comp(ack(), vec![Grf::Proj(3, 2), Grf::Proj(3, 2)]);
    let f = Grf::rec(Grf::Proj(1,1), ack_diag);
    // h(n) = f(n+1,n+1)
    let h = diag_succ(f);
    // h(1) = f(2) = ack^2(2) = ack(41 2^38 - 1) >> f_omega(10^10)
    Grf::comp(h, vec![constant(1, 0)])
}

/// Graham() > Graham's number
pub fn graham() -> Grf {
    // f(n,n) = ack^n(n+1)
    // g(n,n) = f^n(n+1)
    // h(n) = g(n+1,n+1)
    let f = diag_rep(ack());
    let g = diag_rep(f);
    let h = diag_succ(g);
    // h(1) = g(2) = f^2(3) = f(ack^3(4)) > f(ack^2(41 2^38 - 1)) >> f(64) > Graham
    Grf::comp(h, vec![constant(1, 0)])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulate::{simulate, Num};

    fn list2int(xs: &[Num]) -> Num {
        let mut val = 0;
        for x in xs {
            val = (val << 1) + 1;
            val = (val << x) - 1;
        }
        val
    }

    #[test]
    fn test_list2int() {
        assert_eq!(list2int(&[1, 2, 3]), 0b010110111);
        assert_eq!(list2int(&[5, 0, 1]), 0b011111001);
        assert_eq!(list2int(&[1, 0, 0]), 0b0100);
        // Note: Leading 0s are lost in encoding
        assert_eq!(list2int(&[0, 0, 0]), 0b000);
        assert_eq!(list2int(&[]), 0);
    }

    fn eval(grf: &Grf, args: &[Num]) -> Option<Num> {
        let (result, _steps) = simulate(grf, args, 10_000_000);
        result.into_value()
    }

    // ── arity & size ───────────────────────────────────────────────────────────

    #[test]
    fn test_arity_and_size() {
        let cases: &[(&str, &dyn Fn() -> Grf, usize, usize)] = &[
            ("pred", &pred, 1, 3),
            ("not", &not, 1, 5),
            ("sgn", &sgn, 1, 5),
            ("plus2", &plus2, 1, 3),
            ("double", &double, 1, 7),
            ("rmonus", &rmonus, 2, 7),
            ("mod2", &mod2, 1, 9),
            ("shift", &shift, 2, 11),
            ("rmonus_odd", &rmonus_odd, 2, 13),
            ("div2", &div2, 1, 14),
            ("div2k", &div2k, 2, 18),
            ("append", &append, 2, 26),
            ("bit", &bit, 2, 28),
            ("pop_k", &pop_k, 1, 29),
            ("append_n", &append_n, 3, 31),
            ("ack_step", &ack_step, 2, 80),
            ("ack_loop", &ack_loop, 2, 85),
            ("ack_worm", &ack_worm, 1, 86),
            ("init_list", &init_list, 2, 10),
            ("ack", &ack, 2, 97),
            ("omega", &omega, 0, 109),
            ("graham", &graham, 0, 114),
        ];
        for (name, f, arity, size) in cases {
            let g = f();
            assert_eq!(g.arity(), *arity, "{name}: wrong arity");
            assert_eq!(g.size(), *size, "{name}: wrong size");
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
    fn test_append() {
        let f = append();
        assert_eq!(eval(&f, &[0, list2int(&[2])]), Some(list2int(&[2])));
        // Decrement last and append k
        assert_eq!(
            eval(&f, &[1, list2int(&[2])]),
            Some(list2int(&[1, 1]))
        );
        assert_eq!(
            eval(&f, &[2, list2int(&[2])]),
            Some(list2int(&[1, 2]))
        );
        assert_eq!(
            eval(&f, &[3, list2int(&[2])]),
            Some(list2int(&[1, 3]))
        );
        assert_eq!(
            eval(&f, &[2, list2int(&[1, 1])]),
            Some(list2int(&[1, 0, 2]))
        );
    }

    #[test]
    fn test_append_n() {
        // AppendN(n, k, x): [...] + [k] -> [...] + [k-1]*n + [k]
        let f = append_n();

        // Base cases (n = 0): result = x unchanged
        for x in 0..16 {
            assert_eq!(eval(&f, &[0, x, x]), Some(x));
        }

        // [2] -> [1]*n + [2]
        assert_eq!(eval(&f, &[1, 2, list2int(&[2])]), Some(list2int(&[1,2])));
        assert_eq!(eval(&f, &[2, 2, list2int(&[2])]), Some(list2int(&[1,1,2])));
        assert_eq!(eval(&f, &[3, 2, list2int(&[2])]), Some(list2int(&[1,1,1,2])));

        // [1,3] -> [1] + [2]*n + [3]
        assert_eq!(eval(&f, &[1, 3, list2int(&[1,3])]), Some(list2int(&[1,2,3])));
        assert_eq!(eval(&f, &[2, 3, list2int(&[1,3])]), Some(list2int(&[1,2,2,3])));
    }

    #[test]
    fn test_bit() {
        // bit(k, x) = the k-th bit of x
        let f = bit();
        assert_eq!(eval(&f, &[0, 0b101]), Some(1));
        assert_eq!(eval(&f, &[1, 0b101]), Some(0));
        assert_eq!(eval(&f, &[2, 0b101]), Some(1));
        assert_eq!(eval(&f, &[3, 0b101]), Some(0));
        // exhaustive check for small values
        for x in 0u64..16 {
            for k in 0u64..=5 {
                assert_eq!(eval(&f, &[k, x]), Some((x >> k) & 1), "bit({k}, {x})");
            }
        }
    }

    #[test]
    fn test_pop_k() {
        // pop_k(x) = number of trailing 1-bits (length of lowest 1-run)
        let f = pop_k();
        assert_eq!(eval(&f, &[0b0]), Some(0));
        assert_eq!(eval(&f, &[0b1]), Some(1));
        assert_eq!(eval(&f, &[0b10]), Some(0));
        assert_eq!(eval(&f, &[0b11]), Some(2));
        assert_eq!(eval(&f, &[0b111]), Some(3));
        
        // [1,2,4] runs over steps
        for x in 0..3 {
            assert_eq!(eval(&f, &[list2int(&[1,2,x])]), Some(x));
        }
        // [8] runs over steps
        for x in 0..7 {
            assert_eq!(eval(&f, &[list2int(&[x])]), Some(x));
        }
    }

    #[test]
    fn test_ack_step() {
        // AckStep(n, x): x = [...] + [k] -> [...] + [k-1]*(n+1)
        let f = ack_step();
        assert_eq!(eval(&f, &[0, list2int(&[2])]), Some(list2int(&[1])));
        assert_eq!(eval(&f, &[0, list2int(&[5])]), Some(list2int(&[4])));
        assert_eq!(eval(&f, &[0, list2int(&[1,2,3])]), Some(list2int(&[1,2,2])));
        assert_eq!(eval(&f, &[1, list2int(&[2])]), Some(list2int(&[1,1])));
        assert_eq!(eval(&f, &[1, list2int(&[1,2,1])]), Some(list2int(&[1,2,0,0])));
        assert_eq!(eval(&f, &[2, list2int(&[1,0,2])]), Some(list2int(&[1,0,1,1,1])));
    }

    #[test]
    fn test_ack_loop() {
        // AckLoop(m, x): Iterate AckStep m times on list x (with increasing values of n)
        let f = ack_loop();

        // Base cases (m = 0): result = x unchanged
        for x in 0..16 {
            assert_eq!(eval(&f, &[0, x]), Some(x));
        }

        // One ack_step(0, .): [..., k] -> [..., k-1]
        assert_eq!(eval(&f, &[1, list2int(&[1])]), Some(list2int(&[0])));
        assert_eq!(eval(&f, &[1, list2int(&[2])]), Some(list2int(&[1])));
        assert_eq!(eval(&f, &[1, list2int(&[1,2,3])]), Some(list2int(&[1,2,2])));

        // Two ack_steps:
        //      ack_step(0, .): [..., k] -> [..., k-1]
        //      ack_step(1, .): [..., k-1] -> [..., k-2, k-2]
        assert_eq!(eval(&f, &[2, list2int(&[3])]), Some(list2int(&[1,1])));
        assert_eq!(eval(&f, &[2, list2int(&[1,2])]), Some(list2int(&[1,0,0])));
        // [1,1] -> [1,0] -> [1]
        assert_eq!(eval(&f, &[2, list2int(&[1,1])]), Some(list2int(&[1])));

        // [3] -> [2] -> [1,1] -> [1,0,0,0] -> [1,0,0]
        assert_eq!(eval(&f, &[4, list2int(&[3])]), Some(list2int(&[1,0,0])));
        // Too big:
        // [4] -> [3] -> [2,2] -> [2,1,1,1]
        // assert_eq!(eval(&f, &[3, list2int(&[4])]), Some(list2int(&[2,1,1,1])));
    }

    #[test]
    fn test_ack_worm_small() {
        let f = ack_worm();

        // [1] -> [0] = 0
        assert_eq!(eval(&f, &[list2int(&[1])]), Some(1));
        // [2] -> [1] -> [0,0] = 0
        assert_eq!(eval(&f, &[list2int(&[2])]), Some(2));
        // [3] -> [2] -> [1,1] -> [1,0,0,0] -> [1,0,0] -> [1,0] -> [1] -> [0]*7 0
        assert_eq!(eval(&f, &[list2int(&[3])]), Some(7));
        // Too big:
        // [4] -> [3] -> [2,2] -> [2,1,1,1] -> [2,1,1,0,0,0,0] --(4)--> [2,1,1]
        //     -> [2,1] 0^9 --(9)--> [2,1] -> 2 0^19 --(19)--> 2 -> 1^39 ->
        //     -> 1^38 0^40 --> 1^38 -> 1^37 0^81
        //     ---> 0^{41 2^38 - 1}
        // assert_eq!(eval(&f, &[list2int(&[4])]), Some(?));

        // [1,0] -> [1] -> [0,0]
        assert_eq!(eval(&f, &[list2int(&[1,0])]), Some(2));
        // [1,1] -> [1,0] -> [1] -> [0,0,0]
        assert_eq!(eval(&f, &[list2int(&[1,1])]), Some(3));
        // [1,2] -> [1,1] -> [1,0,0] -> [1,0] -> [1] -> [0]*5
        assert_eq!(eval(&f, &[list2int(&[1,2])]), Some(5));
        // Too big:
        // [1,3] -> [1,2] -> [1,1,1] -> [1,1,0,0,0] -> [1,1,0,0] -> [1,1,0] -> [1,1]
        //       -> 1 0^7 --(7)--> [1] -> [0]*15
        // assert_eq!(eval(&f, &[list2int(&[1,3])]), Some(15));
        // [2,0] -> [2] -> [1,1] -> [1,0,0,0] -> [1,0,0] -> [1,0] -> [1] -> [0]*7
        assert_eq!(eval(&f, &[list2int(&[2,0])]), Some(7));
        // Too big:
        // [2,1] -> [2,0] -> [2] -> [1,1,1] -> 1 1 0^4 --(4)--> 1 1 -> 1 0^9
        //       --(9)--> 1 -> 0^19
        // assert_eq!(eval(&f, &[list2int(&[2,1])]), Some(19));

        // 1 0^n --(n)--> 1 -> 0^{n+1}
        for n in 0..6 {
            let mut l = vec![0; n+1];
            l[0] = 1;
            assert_eq!(eval(&f, &[list2int(&l)]), Some((n+1) as u64));
        }

        // 1 1 0^n --(n)--> 1 1 -> 1 0^{n+1} --(n+1)--> 1 -> 0^{2n+3}
        for n in 0..5 {
            let mut l = vec![0; n+2];
            l[0] = 1;
            l[1] = 1;
            assert_eq!(eval(&f, &[list2int(&l)]), Some((2*n+3) as u64));
        }

        // 1^n -> 1^n-1 0 -> 1^n-1 -> 1^n-2 0^3 --> 1^n-2 -> 1^n-3 0^7 ---> 0^{2^n - 1}
        for n in 0..4 {
            let l = vec![1; n];
            assert_eq!(eval(&f, &[list2int(&l)]), Some(2_u64.pow(n as u32) - 1));
        }
    }

    #[test]
    fn ack_worm_compress() {
        use crate::optimize::opt_inline_proj;

        let before = ack_worm();
        assert_eq!(before.size(), 86);
        let after = opt_inline_proj(before);
        assert_eq!(after.size(), 79);
    }

    #[test]
    fn test_init_list() {
        let f = init_list();
        for n in 0u64..12 {
            let x = eval(&f, &[n, n]).unwrap();
            // Check that last n bits are all 1s
            let mask = 2_u64.pow(n as u32) - 1;
            assert_eq!(x & mask, mask, "init_list({n},{n}) = {x}");
        }
    }

    #[test]
    fn graham_compress() {
        use crate::optimize::opt_inline_proj;

        let before = graham();
        assert_eq!(before.size(), 114);
        let after = opt_inline_proj(before);
        assert_eq!(after.size(), 107);
    }
}
