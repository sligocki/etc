import GenRec.Syntax
import Mathlib

namespace GenRec

/-- Evaluates a PRF given an array of arguments (represented as a function from Fin k to Nat) -/
def evalPRF : {k : Nat} → PRF k → (Fin k → Nat) → Nat
| _, PRF.zero _, _ => 0
| _, PRF.succ, args => args ⟨0, by decide⟩ + 1
| _, PRF.proj _ i, args => args i
| _, @PRF.comp k m h gs, args =>
    let inner_args : Fin m → Nat := fun j => evalPRF (gs j) args
    evalPRF h inner_args
| _, @PRF.primRec k g h, args =>
    let n := args ⟨0, Nat.zero_lt_succ k⟩
    let rest : Fin k → Nat := fun j => args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let rec loop : Nat → Nat
      | 0 => evalPRF g rest
      | m + 1 =>
          let acc := loop m
          -- h takes (m, acc, rest...)
          let h_args : Fin (k + 2) → Nat := fun i =>
            if _h1 : i.val = 0 then m
            else if _h2 : i.val = 1 then acc
            else rest ⟨i.val - 2, by omega⟩
          evalPRF h h_args
    loop n

end GenRec
