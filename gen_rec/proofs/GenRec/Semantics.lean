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


/-- An expression representing a partially or fully evaluated PRF state. -/
inductive Expr
| val (n : Nat)
| app {k : Nat} (f : PRF k) (args : Fin k → Expr)

mutual
/-- Big-Step Operational Semantics for PRFs. `ComputesTo expr val` means `expr` evaluates to `val`. -/
inductive ComputesTo : Expr → Expr → Prop
-- Values compute to themselves
| val_refl (n : Nat) : ComputesTo (Expr.val n) (Expr.val n)

-- Zero
| zero {k : Nat} (args : Fin k → Expr) :
    ComputesTo (Expr.app (PRF.zero k) args) (Expr.val 0)

-- Succ
| succ (args : Fin 1 → Expr) (n : Nat) :
    ComputesTo (args 0) (Expr.val n) →
    ComputesTo (Expr.app PRF.succ args) (Expr.val (n + 1))

-- Proj
| proj {k : Nat} (i : Fin k) (args : Fin k → Expr) (n : Nat) :
    ComputesTo (args i) (Expr.val n) →
    ComputesTo (Expr.app (PRF.proj k i) args) (Expr.val n)

-- Comp
| comp {k m : Nat} (h : PRF m) (gs : PRFList k m) (args : Fin k → Expr) (vs : Fin m → Nat) (res : Nat) :
    ComputesToList gs args vs →
    ComputesTo (Expr.app h (fun i => Expr.val (vs i))) (Expr.val res) →
    ComputesTo (Expr.app (PRF.comp h gs) args) (Expr.val res)

-- PrimRec
| rec_zero {k : Nat} (g : PRF k) (h : PRF (k + 2)) (args : Fin (k + 1) → Expr) (vs : Fin k → Nat) (res : Nat) :
    ComputesTo (args 0) (Expr.val 0) →
    (∀ j : Fin k, ComputesTo (args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) (Expr.val (vs j))) →
    ComputesTo (Expr.app g (fun j => Expr.val (vs j))) (Expr.val res) →
    ComputesTo (Expr.app (PRF.primRec g h) args) (Expr.val res)

| rec_succ {k : Nat} (g : PRF k) (h : PRF (k + 2)) (args : Fin (k + 1) → Expr) (n : Nat) (vs : Fin k → Nat) (acc res : Nat) :
    ComputesTo (args 0) (Expr.val (n + 1)) →
    (∀ j : Fin k, ComputesTo (args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) (Expr.val (vs j))) →
    ComputesTo (Expr.app (PRF.primRec g h) (fun i => if h_i : i.val = 0 then Expr.val n else Expr.val (vs ⟨i.val - 1, by omega⟩))) (Expr.val acc) →
    ComputesTo (Expr.app h (fun i => if _h1 : i.val = 0 then Expr.val n else if _h2 : i.val = 1 then Expr.val acc else Expr.val (vs ⟨i.val - 2, by omega⟩))) (Expr.val res) →
    ComputesTo (Expr.app (PRF.primRec g h) args) (Expr.val res)

/-- Evaluates a PRFList to a list of values -/
inductive ComputesToList : {k m : Nat} → PRFList k m → (Fin k → Expr) → (Fin m → Nat) → Prop
| nil {k : Nat} (args : Fin k → Expr) :
    ComputesToList PRFList.nil args (fun i => i.elim0)
| cons {k m : Nat} (g : PRF k) (gs : PRFList k m) (args : Fin k → Expr) (v : Nat) (vs : Fin m → Nat) :
    ComputesTo (Expr.app g args) (Expr.val v) →
    ComputesToList gs args vs →
    ComputesToList (PRFList.cons g gs) args (fun i => if h : i.val = 0 then v else vs ⟨i.val - 1, by omega⟩)
end


/-- Equivalence between the big-step operational semantics and the computational evaluation. -/
theorem evalPRF_iff_ComputesTo {k : Nat} (prf : PRF k) (args : Fin k → Nat) (v : Nat) :
  evalPRF prf args = v ↔ 
  ComputesTo (Expr.app prf (fun i => Expr.val (args i))) (Expr.val v) := sorry

end GenRec
