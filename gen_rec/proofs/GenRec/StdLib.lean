import GenRec.Semantics

open GenRec
open PRF

namespace GenRec.StdLib

def mk_args2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
def mk_args3 (a b c : Nat) : Fin 3 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else c
def mk_args4 (a b c d : Nat) : Fin 4 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

-- 1. OpWrap Succ: if x = 0 then y + 1 else x - 1 (Occurs 38 times)
def op_wrap_succ : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)

-- 2. OpWrap Proj1: if x = 0 then y else x - 1 (Occurs 16 times)
def op_wrap_proj1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)

-- 3. OpWrap Proj2: if x = 0 then y else x - 1 (Occurs 4 times)
def op_wrap_proj2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)

macro "eval_prf" : tactic =>
  `(tactic| simp [evalPRF, evalPRFList, op_wrap_succ, op_wrap_proj1, op_wrap_proj2, mk_args2, mk_args3, mk_args4])

lemma eval_op_wrap_succ (x y : Nat) : evalPRF op_wrap_succ (mk_args2 x y) = if x = 0 then y + 1 else x - 1 := by
  induction x with
  | zero => eval_prf
  | succ x' ih => eval_prf

lemma eval_op_wrap_proj1 (x y : Nat) : evalPRF op_wrap_proj1 (mk_args2 x y) = if x = 0 then y else x - 1 := by
  induction x with
  | zero => eval_prf
  | succ x' ih => eval_prf

lemma eval_op_wrap_proj2 (x y z : Nat) : evalPRF op_wrap_proj2 (mk_args3 x y z) = if x = 0 then y else x - 1 := by
  induction x with
  | zero => eval_prf
  | succ x' ih => eval_prf

end GenRec.StdLib
