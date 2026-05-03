/// A hand-built GRF encoding of a function with Ackermann growth.
use crate::grf;
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
/// M(R(P(1,1), Z3))
/// Arity: 1, Size: 4
pub fn sgn() -> Grf {
    Grf::min(Grf::rec(Grf::Proj(1, 1), Grf::Zero(3)))
}

/// Plus2(x) := x + 2
/// C(S, S)
/// Arity: 1, Size: 3
pub fn plus2() -> Grf {
    Grf::comp(Grf::Succ, vec![Grf::Succ])
}

/// Add(x,y) := x + y
/// R(P(1,1), C(S, P(3,2)))
/// Arity: 2, Size: 5
pub fn add() -> Grf {
    Grf::rec(Grf::Proj(1,1), Grf::comp(Grf::Succ, vec![Grf::Proj(3,2)]))
}

/// RMonus(x,y) := y ∸ x
/// R(P(1,1), C(Pred, P(3,2)))
/// Arity: 2, Size: 7
pub fn rmonus() -> Grf {
    Grf::rec(Grf::Proj(1, 1), Grf::comp(pred(), vec![Grf::Proj(3, 2)]))
}

/// Mod2(x) := x mod 2
/// Arity: 1, Size: 8
pub fn mod2() -> Grf {
    grf!("R(Z0, C(R(S, Z3), P(2,2), Z2))")
}

/// Shift(k,x) := x · 2^k
/// R(P(1,1), C(Add, P(3,2), P(3,2)))
/// Arity: 2, Size: 10
pub fn shift() -> Grf {
    Grf::rec(Grf::Proj(1, 1), Grf::comp(add(), vec![Grf::Proj(3, 2), Grf::Proj(3, 2)]))
}

/// Monus2(x) := x ∸ 2
/// R(Z0, R(Z1, P(3,1)))
/// Arity: 1, Size: 5
pub fn monus2() -> Grf {
    Grf::rec(Grf::Zero(0), Grf::rec(Grf::Zero(1), Grf::Proj(3, 1)))
}

/// RMonusOdd(x,y) := y ∸ (2x + 1)
/// R(Pred, C(Monus2, P(3,2)))
/// Arity: 2, Size: 11
pub fn rmonus_odd() -> Grf {
    Grf::rec(pred(), Grf::comp(monus2(), vec![Grf::Proj(3, 2)]))
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

/// DecAppend(k,x) := x · 2^k ∸ Sgn(k)
///   If k ≥ 1: Decrement last value of list x and append k ([..., a] -> [..., a-1, k])
///   if k = 0: Do nothing
/// C(RMonus, C(Sgn, P(2,1)), Shift)
/// Arity: 2, Size: 26
pub fn dec_append() -> Grf {
    Grf::comp(
        rmonus(),
        vec![Grf::comp(sgn(), vec![Grf::Proj(2, 1)]), shift()],
    )
}

/// DecAppendN(n, k, x): [...] + [k] -> [...] + [k-1]*n + [k]
/// R(P(2,2), C(DecAppend, P(4,3), P(4,2)))
/// Arity: 3, Size: 31
pub fn dec_append_n() -> Grf {
    Grf::rec(
        Grf::Proj(2, 2),
        Grf::comp(dec_append(), vec![Grf::Proj(4, 3), Grf::Proj(4, 2)]),
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
/// C(Div2, C(DecAppendN, P(2,1), C(PopK, P(2,2)), P(2,2)))
/// Arity: 2, Size: 80
pub fn ack_step() -> Grf {
    Grf::comp(
        div2(),
        vec![Grf::comp(
            dec_append_n(),
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

/// AckWorm(x): A version of Hydra game/Goodstein sequence for linear trees
///             (Instead of a branching hydra, it is a linear worm)
///
/// AckWorm([k]) > f_ω(k-2)
///
///     Equivalent to algorithm:
///         N = 0
///         while list x is not empty and not all 0s:
///             N += 1
///             k = pop_last(x)
///             if k > 0: append N copies of (k-1) to x
///         return N
// 
//      Let (N, [..., k]) --> (E_k(N), [...])
//          E_0(N) = N+1
//          E_{k+1}(N) = E_k^{N+1}(N+1)
//      E_k(N) > 2 {k-1} (N+1)
// 
//      Then: AckWorm([a,b,c]) = E_a(E_b(E_c(0))) / 2
//          Note: The / 2 at the end accounts for the fact that we halt
//          early when we get to all 0s (which was not accounted for in
//          the E_k derivation above)
// 
//      AckWorm([k]) = E_k(0)/2 = E_{k-1}(1)/2 = E_{k-2}^2(2)/2 ...
//                   > 2 {k-3} 2 {k-3} 3
//      Which grows faster than all PRFs
// 
//      Guaranteed to halt on all inputs, but it grows faster than all PRF
/// M(AckLoop)
pub fn ack_worm() -> Grf {
    Grf::min(ack_loop())
}
// AckWorm([4]) = 41 2^38 - 1 = [1,1,0,0,38]
// E_0(N) = N+1 = f_0(N)
// E_1(N) = 2N+2 > f_1(N)
// E_2(N) = (N+3) 2^{N+1} - 2 > 2 f_2(N)
// E_k(N) > 2 f_k(N)
// AckWorm([k]) = E_{k-2}^2(2)/2 > f_{k-2}^2(2) > f_{k-2}(10 {k-2} 10) > f_ω(k-2)

/// InitList(n,_) := list ending in a value >= n
/// Arity: 2, Size: 10
pub fn init_list() -> Grf {
    // (n,m) -> (m+2) 2^n - 1
    // A number ending in at least n 1s in binary
    // the (m+2) bit is sort of irrelevant, this just happens
    // to be a cheep GRF that is guaranteed to end in n 1s
    diag_rep(rep_succ(Grf::Succ))
}
// InitList(0,0) = 2 2^0 - 1 = 0b1 = [1]
// InitList(1,1) = 3 2^1 - 1 = 0b101 = [1,1]
// InitList(2,2) = 4 2^2 - 1 = 0b1111 = [4]
// InitList(3,3) = 5 2^3 - 1 = 0b100111 = [1,0,3]
// InitList(4,4) = 6 2^4 - 1 = 0b1011111 = [1,5]
// InitList(5,5) = 7 2^5 - 1 = 0b11011111 = [2,5]
// InitList(6,6) = 8 2^6 - 1 = 0b111111111 = [9]

/// Ack(n,_) > AckWorm([n])
///     Dominates all PRF
/// C(AckWorm, InitList)
/// Arity: 2
pub fn ack() -> Grf {
    Grf::comp(ack_worm(), vec![init_list()])
}
// Ack(1) = AckWorm([1,1]) = 3
// Ack(2) = AckWorm([4]) = 41 2^38 - 1
// Ack(3) = AckWorm([1,0,3]) = 16
// Ack(4) = AckWorm([1,5]) > 10 ^^ 10^96 > f_ω(3)
// Ack(5) = AckWorm([2,5]) > 10 ^^ 10^96 > f_ω(3)
// Ack(6) = AckWorm([9]) > f_ω(7)

/// Omega() > f_ω(10^13)
pub fn omega() -> Grf {
    // ack_diag(n) = ack(n,n)
    let ack_diag = Grf::comp(ack(), vec![Grf::Proj(3, 2), Grf::Proj(3, 2)]);
    // f(n,n) = ack_diag^n(n)
    let f = Grf::rec(Grf::Proj(1,1), ack_diag);
    // h(n) = f(n+1,n+1)
    let h = diag_succ(f);
    // h(1) = f(2,2) = ack^2(2) = ack(41 2^38 - 1) > f_ω(10^13)
    Grf::comp(h, vec![constant(1, 0)])
}

/// Omega3() > {f_ω}^3(3)
pub fn omega3() -> Grf {
    // f(n,n) = ack^n(n+1) > f_{ω+1}(n)
    let f = diag_rep(ack());
    // h(n) = f(n+1,n+1)
    let h = diag_succ(f);
    // h(2) = f(3,3) = ack^3(4) = ack^2(10 ^^ 10^96) > {f_ω}^3(3)
    Grf::comp(h, vec![constant(2, 0)])
}

/// Omega4() > {f_ω}^4(3)
pub fn omega4() -> Grf {
    // f(n,n) = ack^n(n+1) > f_{ω+1}(n)
    let f = diag_rep(ack());
    // h(n) = f(n+1,n+1)
    let h = diag_succ(f);
    // h(3) = f(4,4) = ack^4(5) = ack^3(10 ^^ 10^96) > {f_ω}^4(3)
    Grf::comp(h, vec![constant(3, 0)])
}

/// Graham() > Graham's number
pub fn graham() -> Grf {
    // f(n,n) = ack^n(n+1) > f_{ω+1}(n)
    let f = diag_rep(ack());
    // g(n,n) = f^n(n+1) > f_{ω+2}(n)
    let g = diag_rep(f);
    // h(n) = g(n+1,n+1)
    let h = diag_succ(g);
    // h(1) = g(2) = f^2(3) = f(ack^3(4)) > f(ack^2(41 2^38 - 1))
    //      > f_{ω+1}(f_ω^2(10^13)) >> f_{ω+1}(64) > Graham
    Grf::comp(h, vec![constant(1, 0)])
}
