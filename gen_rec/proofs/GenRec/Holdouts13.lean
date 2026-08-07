import GenRec.Syntax
import GenRec.Semantics

open GenRec

namespace Holdouts13

-- Translating holdout 0
-- M(C(R(Z1,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_0 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

def mk_args2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
def mk_args3 (a b c : Nat) : Fin 3 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else c

def H0_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H0_c : PRF 2 := PRF.primRec (PRF.zero 1) H0_h

lemma H0_comp (x : Nat) : evalPRF holdout_0 (fun _ => x) = evalPRF H0_c (mk_args2 (x + 1) 0) := by
  change evalPRF H0_c (fun j => evalPRFList prf_list![PRF.succ, PRF.zero 1] j (fun _ => x)) = evalPRF H0_c (mk_args2 (x + 1) 0)
  apply congrArg (evalPRF H0_c)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

lemma H0_h_base : evalPRF H0_h (mk_args3 0 1 0) = 1 := by rfl
lemma H0_h_base_0 : evalPRF H0_h (mk_args3 0 0 0) = 1 := by rfl
lemma H0_h_step (m acc y : Nat) : evalPRF H0_h (mk_args3 (m + 1) acc y) = evalPRF H0_h (mk_args3 m acc y) := by rfl

lemma H0_h_const (m : Nat) : evalPRF H0_h (mk_args3 m 1 0) = 1 := by
  induction m with
  | zero => exact H0_h_base
  | succ m ih => rw [H0_h_step]; exact ih

lemma H0_c_step (x : Nat) : evalPRF H0_c (mk_args2 (x + 1) 0) = evalPRF H0_h (mk_args3 x (evalPRF H0_c (mk_args2 x 0)) 0) := by rfl

lemma H0_c_val (x : Nat) : evalPRF H0_c (mk_args2 (x + 1) 0) = 1 := by
  induction x with
  | zero =>
    rw [H0_c_step 0]
    have h0 : evalPRF H0_c (mk_args2 0 0) = 0 := by rfl
    rw [h0]
    exact H0_h_base_0
  | succ x ih =>
    rw [H0_c_step (x + 1)]
    rw [ih]
    exact H0_h_const (x + 1)

-- Proof produced in ~60 minutes (initial discovery of the Ind Const template)
theorem holdout_0_diverges : ∀ x, evalPRF holdout_0 (fun _ => x) > 0 := by
  intro x
  rw [H0_comp x, H0_c_val x]
  exact Nat.zero_lt_one

-- Translating holdout 1
-- M(C(R(P(1,1),R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2))),S,S))
def holdout_1 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

theorem holdout_1_diverges : ∀ x, evalPRF holdout_1 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 2
-- M(C(R(P(1,1),R(R(S,R(Z2,P(4,1))),P(4,2))),S,P(1,1)))
def holdout_2 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_2_diverges : ∀ x, evalPRF holdout_2 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 3
-- M(C(R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_3 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

def H3_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H3_c : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H3_h
lemma H3_comp (x : Nat) : evalPRF holdout_3 (fun _ => x) = evalPRF H3_c (mk_args2 (x + 1) 0) := by
  change evalPRF H3_c (fun j => evalPRFList prf_list![PRF.succ, PRF.zero 1] j (fun _ => x)) = evalPRF H3_c (mk_args2 (x + 1) 0)
  apply congrArg (evalPRF H3_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl
lemma H3_c_step (x : Nat) : evalPRF H3_c (mk_args2 (x + 1) 0) = evalPRF H3_h (mk_args3 x (evalPRF H3_c (mk_args2 x 0)) 0) := by rfl
lemma H3_h_base_1 (m : Nat) : evalPRF H3_h (mk_args3 m 1 0) = 1 := by
  induction m with | zero => rfl | succ m ih => rw [show evalPRF H3_h (mk_args3 (m + 1) 1 0) = evalPRF H3_h (mk_args3 m 1 0) by rfl, ih]
lemma H3_c_val (x : Nat) : evalPRF H3_c (mk_args2 (x + 1) 0) = 1 := by
  induction x with
  | zero => rfl
  | succ x ih => rw [H3_c_step (x + 1), ih]; exact H3_h_base_1 (x + 1)

-- Proof produced in ~1 minute (adapted from Ind Const template)
theorem holdout_3_diverges : ∀ x, evalPRF holdout_3 (fun _ => x) > 0 := by
  intro x
  rw [H3_comp x, H3_c_val x]
  exact Nat.zero_lt_one

-- Translating holdout 4
-- M(C(R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,S))
def holdout_4 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

theorem holdout_4_diverges : ∀ x, evalPRF holdout_4 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 5
-- M(C(R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2))),S,P(1,1)))
def holdout_5 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_5_diverges : ∀ x, evalPRF holdout_5 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 6
-- M(C(R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2))),S,S))
def holdout_6 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

theorem holdout_6_diverges : ∀ x, evalPRF holdout_6 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 7
-- M(C(R(S,C(R(Z0,R(S,P(3,1))),P(3,2))),P(1,1),Z1))
def holdout_7 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1]

def H7_h : PRF 3 := PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)]
def H7_c : PRF 2 := PRF.primRec (PRF.succ) H7_h
lemma H7_comp (x : Nat) : evalPRF holdout_7 (fun _ => x) = evalPRF H7_c (mk_args2 x 0) := by
  change evalPRF H7_c (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1] j (fun _ => x)) = evalPRF H7_c (mk_args2 x 0)
  apply congrArg (evalPRF H7_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl
lemma H7_c_step (x : Nat) : evalPRF H7_c (mk_args2 (x + 1) 0) = evalPRF H7_h (mk_args3 x (evalPRF H7_c (mk_args2 x 0)) 0) := by rfl
lemma H7_c_val (x : Nat) : evalPRF H7_c (mk_args2 x 0) = 1 := by
  induction x with | zero => rfl | succ x ih => rw [H7_c_step x, ih]; rfl

-- Proof produced in ~1 minute (adapted from Ind Const template)
theorem holdout_7_diverges : ∀ x, evalPRF holdout_7 (fun _ => x) > 0 := by
  intro x
  rw [H7_comp x, H7_c_val x]
  exact Nat.zero_lt_one

-- Translating holdout 8
-- M(C(R(S,C(R(Z0,R(S,P(3,1))),P(3,2))),S,Z1))
def holdout_8 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)])) prf_list![PRF.succ, PRF.zero 1]

def H8_h : PRF 3 := PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)]
def H8_c : PRF 2 := PRF.primRec (PRF.succ) H8_h
lemma H8_comp (x : Nat) : evalPRF holdout_8 (fun _ => x) = evalPRF H8_c (mk_args2 (x + 1) 0) := by
  change evalPRF H8_c (fun j => evalPRFList prf_list![PRF.succ, PRF.zero 1] j (fun _ => x)) = evalPRF H8_c (mk_args2 (x + 1) 0)
  apply congrArg (evalPRF H8_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl
lemma H8_c_step (x : Nat) : evalPRF H8_c (mk_args2 (x + 1) 0) = evalPRF H8_h (mk_args3 x (evalPRF H8_c (mk_args2 x 0)) 0) := by rfl
lemma H8_c_val (x : Nat) : evalPRF H8_c (mk_args2 (x + 1) 0) = 1 := by
  induction x with
  | zero => rfl
  | succ x ih => rw [H8_c_step (x + 1), ih]; rfl

-- Proof produced in ~1 minute (adapted from Ind Const template)
theorem holdout_8_diverges : ∀ x, evalPRF holdout_8 (fun _ => x) > 0 := by
  intro x
  rw [H8_comp x, H8_c_val x]
  exact Nat.zero_lt_one

-- Translating holdout 9
-- M(C(R(S,R(P(2,1),R(R(P(2,2),P(4,1)),P(5,2)))),P(1,1),P(1,1)))
def holdout_9 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) ((PRF.proj 5 ⟨1, by decide⟩))))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_9_diverges : ∀ x, evalPRF holdout_9 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 10
-- M(C(R(S,R(P(2,1),R(R(P(2,2),P(4,1)),P(5,2)))),S,S))
def holdout_10 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) ((PRF.proj 5 ⟨1, by decide⟩))))) prf_list![PRF.succ, PRF.succ]

theorem holdout_10_diverges : ∀ x, evalPRF holdout_10 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 11
-- M(C(R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2))),P(1,1),Z1))
def holdout_11 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1]

def H11_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H11_c : PRF 2 := PRF.primRec (PRF.succ) H11_h
lemma H11_comp (x : Nat) : evalPRF holdout_11 (fun _ => x) = evalPRF H11_c (mk_args2 x 0) := by
  change evalPRF H11_c (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1] j (fun _ => x)) = evalPRF H11_c (mk_args2 x 0)
  apply congrArg (evalPRF H11_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl
lemma H11_c_step (x : Nat) : evalPRF H11_c (mk_args2 (x + 1) 0) = evalPRF H11_h (mk_args3 x (evalPRF H11_c (mk_args2 x 0)) 0) := by rfl
lemma H11_h_base_1 (m : Nat) : evalPRF H11_h (mk_args3 m 1 0) = 1 := by
  induction m with | zero => rfl | succ m ih => rw [show evalPRF H11_h (mk_args3 (m + 1) 1 0) = evalPRF H11_h (mk_args3 m 1 0) by rfl, ih]
lemma H11_c_val (x : Nat) : evalPRF H11_c (mk_args2 x 0) = 1 := by
  induction x with | zero => rfl | succ x ih => rw [H11_c_step x, ih]; exact H11_h_base_1 x

-- Proof produced in ~1 minute (adapted from Ind Const template)
theorem holdout_11_diverges : ∀ x, evalPRF holdout_11 (fun _ => x) > 0 := by
  intro x
  rw [H11_comp x, H11_c_val x]
  exact Nat.zero_lt_one

-- Translating holdout 12
-- M(C(R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_12 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

def H12_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H12_c : PRF 2 := PRF.primRec (PRF.succ) H12_h
lemma H12_comp (x : Nat) : evalPRF holdout_12 (fun _ => x) = evalPRF H12_c (mk_args2 (x + 1) 0) := by
  change evalPRF H12_c (fun j => evalPRFList prf_list![PRF.succ, PRF.zero 1] j (fun _ => x)) = evalPRF H12_c (mk_args2 (x + 1) 0)
  apply congrArg (evalPRF H12_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl
lemma H12_c_step (x : Nat) : evalPRF H12_c (mk_args2 (x + 1) 0) = evalPRF H12_h (mk_args3 x (evalPRF H12_c (mk_args2 x 0)) 0) := by rfl
lemma H12_h_base_1 (m : Nat) : evalPRF H12_h (mk_args3 m 1 0) = 1 := by
  induction m with | zero => rfl | succ m ih => rw [show evalPRF H12_h (mk_args3 (m + 1) 1 0) = evalPRF H12_h (mk_args3 m 1 0) by rfl, ih]
lemma H12_c_val (x : Nat) : evalPRF H12_c (mk_args2 (x + 1) 0) = 1 := by
  induction x with
  | zero => rfl
  | succ x ih => rw [H12_c_step (x + 1), ih]; exact H12_h_base_1 (x + 1)

-- Proof produced in ~1 minute (adapted from Ind Const template)
theorem holdout_12_diverges : ∀ x, evalPRF holdout_12 (fun _ => x) > 0 := by
  intro x
  rw [H12_comp x, H12_c_val x]
  exact Nat.zero_lt_one

-- Translating holdout 13
-- M(C(R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,P(1,1)))
def holdout_13 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_13_diverges : ∀ x, evalPRF holdout_13 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 14
-- M(R(C(S,Z0),R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1)))))
def holdout_14 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

theorem holdout_14_diverges : ∀ x, evalPRF holdout_14 (fun _ => x) > 0 := by
  sorry

end Holdouts13
