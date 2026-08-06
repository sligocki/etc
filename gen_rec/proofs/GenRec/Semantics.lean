import GenRec.Syntax
import Mathlib

namespace GenRec

mutual
/-- Evaluates a PRF given an array of arguments (represented as a function from Fin k to Nat) -/
def evalPRF : {k : Nat} → PRF k → (Fin k → Nat) → Nat
| _, PRF.zero _, _ => 0
| _, PRF.succ, args => args ⟨0, by decide⟩ + 1
| _, PRF.proj _ i, args => args i
| _, @PRF.comp k m h gs, args =>
    let inner_args : Fin m → Nat := fun j => evalPRFList gs j args
    evalPRF h inner_args
| _, @PRF.primRec k g h, args =>
    let n := args ⟨0, Nat.zero_lt_succ k⟩
    let rest : Fin k → Nat := fun j => args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let step (m : Nat) (acc : Nat) : Nat :=
      let h_args : Fin (k + 2) → Nat := fun i =>
        if _h1 : i.val = 0 then m
        else if _h2 : i.val = 1 then acc
        else rest ⟨i.val - 2, by omega⟩
      evalPRF h h_args
    n.recOn (evalPRF g rest) step

/-- Evaluates a list of PRFs -/
def evalPRFList : {k m : Nat} → PRFList k m → Fin m → (Fin k → Nat) → Nat
| _, _, PRFList.nil, i, _ => i.elim0
| _, _, PRFList.cons g _, ⟨0, _⟩, args => evalPRF g args
| _, _, PRFList.cons _ gs, ⟨i + 1, h_i⟩, args =>
    evalPRFList gs ⟨i, Nat.lt_of_succ_lt_succ h_i⟩ args
end

end GenRec
