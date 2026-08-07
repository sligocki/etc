import GenRec.Syntax
import GenRec.Semantics

open GenRec

namespace Holdouts13


-- General
def mk_args2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
def mk_args3 (a b c : Nat) : Fin 3 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else c


-- Translating holdout 0
-- M(C(R(Z1,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_0 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

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

def H1_h : PRF 3 := PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H1_c : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H1_h

lemma H1_comp (x : Nat) : evalPRF holdout_1 (fun _ => x) = evalPRF H1_c (mk_args2 (x + 1) (x + 1)) := by
  change evalPRF H1_c (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H1_c (mk_args2 (x + 1) (x + 1))
  apply congrArg (evalPRF H1_c)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

def H1_g_outer (u v : Nat) : Nat :=
  match u with
  | 0 => v
  | 1 => v
  | u' + 2 => u'

def H1_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H1_g_outer (H1_c_val x' y) y

lemma H1_g_outer_add_two (u v : Nat) : H1_g_outer (u + 2) v = u := by rfl

lemma H1_c_val_leq (x y : Nat) (hx : x ≤ y / 2) : H1_c_val x y = y - 2 * x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have h1 : x ≤ y / 2 := by omega
    have h2 : H1_c_val x y = y - 2 * x := ih h1
    have h_c : H1_c_val (x + 1) y = H1_g_outer (H1_c_val x y) y := by rfl
    have h_c2 : H1_c_val (x + 1) y = H1_g_outer (y - 2 * x) y := Eq.trans h_c (congrArg (fun z => H1_g_outer z y) h2)
    have h3 : y - 2 * x = (y - 2 * x - 2) + 2 := by omega
    have h_c3 : H1_c_val (x + 1) y = H1_g_outer ((y - 2 * x - 2) + 2) y := Eq.trans h_c2 (congrArg (fun z => H1_g_outer z y) h3)
    have h_c4 : H1_c_val (x + 1) y = y - 2 * x - 2 := Eq.trans h_c3 (H1_g_outer_add_two (y - 2 * x - 2) y)
    have h_final : y - 2 * x - 2 = y - 2 * (x + 1) := by omega
    exact Eq.trans h_c4 h_final

lemma H1_c_val_period (x y : Nat) : H1_c_val (x + y / 2 + 1) y = H1_c_val x y := by
  induction x with
  | zero =>
    have ht : 0 + y / 2 + 1 = y / 2 + 1 := by omega
    rw [ht]
    have h_c : H1_c_val (y / 2 + 1) y = H1_g_outer (H1_c_val (y / 2) y) y := by rfl
    rw [h_c]
    have h_val : H1_c_val (y / 2) y = y - 2 * (y / 2) := H1_c_val_leq (y / 2) y (by omega)
    rw [h_val]
    have h_cases : y - 2 * (y / 2) = 0 ∨ y - 2 * (y / 2) = 1 := by omega
    cases h_cases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr h1 =>
      rw [h1]
      rfl
  | succ x ih =>
    have h1 : H1_c_val (x + 1 + y / 2 + 1) y = H1_c_val (x + y / 2 + 1 + 1) y := by
      have h_eq : x + 1 + y / 2 + 1 = x + y / 2 + 1 + 1 := by omega
      rw [h_eq]
    rw [h1]
    have h2 : H1_c_val (x + y / 2 + 1 + 1) y = H1_g_outer (H1_c_val (x + y / 2 + 1) y) y := by rfl
    rw [h2]
    rw [ih]
    rfl

lemma H1_c_val_diag_even (k : Nat) (hk : k > 0) : H1_c_val (2 * k) (2 * k) = 2 := by
  have H : H1_c_val (2 * k) (2 * k) = H1_c_val (k - 1 + (2 * k) / 2 + 1) (2 * k) := by
    have h_eq : 2 * k = k - 1 + (2 * k) / 2 + 1 := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  rw [H1_c_val_period (k - 1) (2 * k)]
  have h_leq : k - 1 ≤ (2 * k) / 2 := by omega
  have h_val := H1_c_val_leq (k - 1) (2 * k) h_leq
  have h_eq : 2 * k - 2 * (k - 1) = 2 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H1_c_val_diag_odd (k : Nat) : H1_c_val (2 * k + 1) (2 * k + 1) = 1 := by
  have H : H1_c_val (2 * k + 1) (2 * k + 1) = H1_c_val (k + (2 * k + 1) / 2 + 1) (2 * k + 1) := by
    have h_eq : 2 * k + 1 = k + (2 * k + 1) / 2 + 1 := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  rw [H1_c_val_period k (2 * k + 1)]
  have h_leq : k ≤ (2 * k + 1) / 2 := by omega
  have h_val := H1_c_val_leq k (2 * k + 1) h_leq
  have h_eq : 2 * k + 1 - 2 * k = 1 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H1_c_val_diag_pos (y : Nat) (hy : y > 0) : H1_c_val y y > 0 := by
  have h_cases : (∃ k, y = 2 * k) ∨ (∃ k, y = 2 * k + 1) := by
    have hm : y % 2 = 0 ∨ y % 2 = 1 := by omega
    cases hm with
    | inl h0 =>
      left
      use (y / 2)
      omega
    | inr h1 =>
      right
      use (y / 2)
      omega
  cases h_cases with
  | inl he =>
    rcases he with ⟨k, hk⟩
    have hk_pos : k > 0 := by omega
    have h_val := H1_c_val_diag_even k hk_pos
    rw [hk]
    rw [h_val]
    exact by decide
  | inr ho =>
    rcases ho with ⟨k, hk⟩
    have h_val := H1_c_val_diag_odd k
    rw [hk]
    rw [h_val]
    exact by decide

lemma H1_c_step (x y : Nat) : evalPRF H1_c (mk_args2 (x + 1) y) = evalPRF H1_h (mk_args3 x (evalPRF H1_c (mk_args2 x y)) y) := by
  cases x with
  | zero => rfl
  | succ x => rfl

lemma H1_h_eq (m acc y : Nat) : evalPRF H1_h (mk_args3 m acc y) = H1_g_outer acc y := by
  induction m with
  | zero =>
    change (evalPRF (PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 acc y)) = H1_g_outer acc y
    induction acc with
    | zero => rfl
    | succ a ih_a =>
      change (evalPRF (PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)) (mk_args3 a (evalPRF (PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 a y)) y)) = H1_g_outer (a + 1) y
      induction a with
      | zero => rfl
      | succ a' ih_a' => rfl
  | succ m ih =>
    change evalPRF H1_h (mk_args3 m acc y) = H1_g_outer acc y
    exact ih

lemma H1_c_val_eq (x y : Nat) : evalPRF H1_c (mk_args2 x y) = H1_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have step : evalPRF H1_c (mk_args2 (x + 1) y) = evalPRF H1_h (mk_args3 x (evalPRF H1_c (mk_args2 x y)) y) := H1_c_step x y
    have h_eq : evalPRF H1_h (mk_args3 x (evalPRF H1_c (mk_args2 x y)) y) = H1_g_outer (evalPRF H1_c (mk_args2 x y)) y := H1_h_eq x (evalPRF H1_c (mk_args2 x y)) y
    have h_step2 : H1_g_outer (evalPRF H1_c (mk_args2 x y)) y = H1_g_outer (H1_c_val x y) y := by rw [ih]
    have h_def : H1_g_outer (H1_c_val x y) y = H1_c_val (x + 1) y := by rfl
    exact Eq.trans step (Eq.trans h_eq (Eq.trans h_step2 h_def))

-- Proof produced in ~45 minutes (formalizing Sub Cycle template with cases/reduction optimizations)
theorem holdout_1_diverges : ∀ x, evalPRF holdout_1 (fun _ => x) > 0 := by
  intro x
  rw [H1_comp x]
  rw [H1_c_val_eq (x + 1) (x + 1)]
  have h_pos : x + 1 > 0 := by omega
  exact H1_c_val_diag_pos (x + 1) h_pos

-- Translating holdout 2
-- M(C(R(P(1,1),R(R(S,R(Z2,P(4,1))),P(4,2))),S,P(1,1)))
def holdout_2 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

def H2_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H2_c : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H2_h

def H2_g_outer (u v : Nat) : Nat :=
  match u with
  | 0 => v + 1
  | 1 => 0
  | u' + 2 => u'

def H2_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H2_g_outer (H2_c_val x' y) y

lemma H2_g_outer_add_two (u v : Nat) : H2_g_outer (u + 2) v = u := by rfl

lemma H2_c_val_leq (x y : Nat) (hx : x ≤ y / 2) : H2_c_val x y = y - 2 * x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have h1 : x ≤ y / 2 := by omega
    have h2 : H2_c_val x y = y - 2 * x := ih h1
    have h_c : H2_c_val (x + 1) y = H2_g_outer (H2_c_val x y) y := by rfl
    have h_c2 : H2_c_val (x + 1) y = H2_g_outer (y - 2 * x) y := Eq.trans h_c (congrArg (fun z => H2_g_outer z y) h2)
    have h3 : y - 2 * x = (y - 2 * x - 2) + 2 := by omega
    have h_c3 : H2_c_val (x + 1) y = H2_g_outer ((y - 2 * x - 2) + 2) y := Eq.trans h_c2 (congrArg (fun z => H2_g_outer z y) h3)
    have h_c4 : H2_c_val (x + 1) y = y - 2 * x - 2 := Eq.trans h_c3 (H2_g_outer_add_two (y - 2 * x - 2) y)
    have h_final : y - 2 * x - 2 = y - 2 * (x + 1) := by omega
    exact Eq.trans h_c4 h_final

lemma H2_even_phase2 (k j : Nat) (hj : j ≤ k) : H2_c_val (k + 1 + j) (2 * k) = 2 * k + 1 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H2_c_val (k + 1) (2 * k) = H2_g_outer (H2_c_val k (2 * k)) (2 * k) := by rfl
    rw [hc]
    have hval : H2_c_val k (2 * k) = 2 * k - 2 * k := H2_c_val_leq k (2 * k) (by omega)
    have h0 : 2 * k - 2 * k = 0 := by omega
    rw [h0] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H2_c_val ((k + 1 + j) + 1) (2 * k) = H2_g_outer (H2_c_val (k + 1 + j) (2 * k)) (2 * k) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 1 - 2 * j = (2 * k + 1 - 2 * j - 2) + 2 := by omega
    have hc2 : H2_g_outer (2 * k + 1 - 2 * j) (2 * k) = H2_g_outer ((2 * k + 1 - 2 * j - 2) + 2) (2 * k) := congrArg (fun z => H2_g_outer z (2 * k)) h_inner
    rw [hc2]
    rw [H2_g_outer_add_two]
    omega

lemma H2_odd_phase2 (k j : Nat) (hj : j ≤ k) : H2_c_val (k + 2 + j) (2 * k + 1) = 2 * k + 2 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 2 + 0 = k + 2 := by omega
    rw [ht]
    have hc : H2_c_val (k + 2) (2 * k + 1) = H2_g_outer (H2_c_val (k + 1) (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    have hc_inner : H2_c_val (k + 1) (2 * k + 1) = H2_g_outer (H2_c_val k (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc_inner]
    have hval : H2_c_val k (2 * k + 1) = 2 * k + 1 - 2 * k := H2_c_val_leq k (2 * k + 1) (by omega)
    have h1 : 2 * k + 1 - 2 * k = 1 := by omega
    rw [h1] at hval
    rw [hval]
    have hg1 : H2_g_outer 1 (2 * k + 1) = 0 := by rfl
    rw [hg1]
    have hg0 : H2_g_outer 0 (2 * k + 1) = 2 * k + 1 + 1 := by rfl
    rw [hg0]
    omega
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 2 + (j + 1) = (k + 2 + j) + 1 := by omega
    rw [h1]
    have hc : H2_c_val ((k + 2 + j) + 1) (2 * k + 1) = H2_g_outer (H2_c_val (k + 2 + j) (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 2 - 2 * j = (2 * k + 2 - 2 * j - 2) + 2 := by omega
    have hc2 : H2_g_outer (2 * k + 2 - 2 * j) (2 * k + 1) = H2_g_outer ((2 * k + 2 - 2 * j - 2) + 2) (2 * k + 1) := congrArg (fun z => H2_g_outer z (2 * k + 1)) h_inner
    rw [hc2]
    rw [H2_g_outer_add_two]
    omega

lemma H2_c_val_diag_even (k : Nat) : H2_c_val (2 * k + 1) (2 * k) = 1 := by
  have H : H2_c_val (2 * k + 1) (2 * k) = H2_c_val (k + 1 + k) (2 * k) := by
    have h_eq : 2 * k + 1 = k + 1 + k := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H2_even_phase2 k k (by omega)
  have h_eq : 2 * k + 1 - 2 * k = 1 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H2_c_val_diag_odd (k : Nat) : H2_c_val (2 * k + 2) (2 * k + 1) = 2 := by
  have H : H2_c_val (2 * k + 2) (2 * k + 1) = H2_c_val (k + 2 + k) (2 * k + 1) := by
    have h_eq : 2 * k + 2 = k + 2 + k := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H2_odd_phase2 k k (by omega)
  have h_eq : 2 * k + 2 - 2 * k = 2 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H2_c_val_diag_pos (y : Nat) : H2_c_val (y + 1) y > 0 := by
  have h_cases : (∃ k, y = 2 * k) ∨ (∃ k, y = 2 * k + 1) := by
    have hm : y % 2 = 0 ∨ y % 2 = 1 := by omega
    cases hm with
    | inl h0 =>
      left
      use (y / 2)
      omega
    | inr h1 =>
      right
      use (y / 2)
      omega
  cases h_cases with
  | inl he =>
    rcases he with ⟨k, hk⟩
    have h_val := H2_c_val_diag_even k
    rw [hk]
    rw [h_val]
    exact by decide
  | inr ho =>
    rcases ho with ⟨k, hk⟩
    have h_val := H2_c_val_diag_odd k
    rw [hk]
    have H2 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    rw [H2]
    rw [h_val]
    exact by decide

lemma H2_c_step (x y : Nat) : evalPRF H2_c (mk_args2 (x + 1) y) = evalPRF H2_h (mk_args3 x (evalPRF H2_c (mk_args2 x y)) y) := by
  cases x with
  | zero => rfl
  | succ x => rfl

lemma H2_h_eq (m acc y : Nat) : evalPRF H2_h (mk_args3 m acc y) = H2_g_outer acc y := by
  induction m with
  | zero =>
    change (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.zero 2) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 acc y)) = H2_g_outer acc y
    induction acc with
    | zero => rfl
    | succ a ih_a =>
      change (evalPRF (PRF.primRec (PRF.zero 2) (PRF.proj 4 ⟨0, by decide⟩)) (mk_args3 a (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.zero 2) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 a y)) y)) = H2_g_outer (a + 1) y
      induction a with
      | zero => rfl
      | succ a' ih_a' => rfl
  | succ m ih =>
    change evalPRF H2_h (mk_args3 m acc y) = H2_g_outer acc y
    exact ih

lemma H2_c_val_eq (x y : Nat) : evalPRF H2_c (mk_args2 x y) = H2_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have step : evalPRF H2_c (mk_args2 (x + 1) y) = evalPRF H2_h (mk_args3 x (evalPRF H2_c (mk_args2 x y)) y) := H2_c_step x y
    have h_eq : evalPRF H2_h (mk_args3 x (evalPRF H2_c (mk_args2 x y)) y) = H2_g_outer (evalPRF H2_c (mk_args2 x y)) y := H2_h_eq x (evalPRF H2_c (mk_args2 x y)) y
    have h_step2 : H2_g_outer (evalPRF H2_c (mk_args2 x y)) y = H2_g_outer (H2_c_val x y) y := by rw [ih]
    have h_def : H2_g_outer (H2_c_val x y) y = H2_c_val (x + 1) y := by rfl
    exact Eq.trans step (Eq.trans h_eq (Eq.trans h_step2 h_def))

lemma H2_comp (x : Nat) : evalPRF holdout_2 (fun _ => x) = evalPRF H2_c (mk_args2 (x + 1) x) := by
  change evalPRF H2_c (fun j => evalPRFList prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H2_c (mk_args2 (x + 1) x)
  apply congrArg (evalPRF H2_c)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

-- Proof produced in ~45 minutes (adapted from Sub Cycle template)
theorem holdout_2_diverges : ∀ x, evalPRF holdout_2 (fun _ => x) > 0 := by
  intro x
  rw [H2_comp x]
  rw [H2_c_val_eq (x + 1) x]
  exact H2_c_val_diag_pos x

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

def H4_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H4_c : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H4_h

def H4_g_outer (u v : Nat) : Nat :=
  match u with
  | 0 => v + 1
  | 1 => v + 1
  | u' + 2 => u'

def H4_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H4_g_outer (H4_c_val x' y) y

lemma H4_g_outer_add_two (u v : Nat) : H4_g_outer (u + 2) v = u := by rfl

lemma H4_c_val_leq (x y : Nat) (hx : x ≤ y / 2) : H4_c_val x y = y - 2 * x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have h1 : x ≤ y / 2 := by omega
    have h2 : H4_c_val x y = y - 2 * x := ih h1
    have h_c : H4_c_val (x + 1) y = H4_g_outer (H4_c_val x y) y := by rfl
    have h_c2 : H4_c_val (x + 1) y = H4_g_outer (y - 2 * x) y := Eq.trans h_c (congrArg (fun z => H4_g_outer z y) h2)
    have h3 : y - 2 * x = (y - 2 * x - 2) + 2 := by omega
    have h_c3 : H4_c_val (x + 1) y = H4_g_outer ((y - 2 * x - 2) + 2) y := Eq.trans h_c2 (congrArg (fun z => H4_g_outer z y) h3)
    have h_c4 : H4_c_val (x + 1) y = y - 2 * x - 2 := Eq.trans h_c3 (H4_g_outer_add_two (y - 2 * x - 2) y)
    have h_final : y - 2 * x - 2 = y - 2 * (x + 1) := by omega
    exact Eq.trans h_c4 h_final

lemma H4_even_phase2 (k j : Nat) (hj : j ≤ k) : H4_c_val (k + 1 + j) (2 * k) = 2 * k + 1 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H4_c_val (k + 1) (2 * k) = H4_g_outer (H4_c_val k (2 * k)) (2 * k) := by rfl
    rw [hc]
    have hval : H4_c_val k (2 * k) = 2 * k - 2 * k := H4_c_val_leq k (2 * k) (by omega)
    have h0 : 2 * k - 2 * k = 0 := by omega
    rw [h0] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H4_c_val ((k + 1 + j) + 1) (2 * k) = H4_g_outer (H4_c_val (k + 1 + j) (2 * k)) (2 * k) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 1 - 2 * j = (2 * k + 1 - 2 * j - 2) + 2 := by omega
    have hc2 : H4_g_outer (2 * k + 1 - 2 * j) (2 * k) = H4_g_outer ((2 * k + 1 - 2 * j - 2) + 2) (2 * k) := congrArg (fun z => H4_g_outer z (2 * k)) h_inner
    rw [hc2]
    rw [H4_g_outer_add_two]
    omega

lemma H4_odd_phase2 (k j : Nat) (hj : j ≤ k) : H4_c_val (k + 1 + j) (2 * k + 1) = 2 * k + 2 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H4_c_val (k + 1) (2 * k + 1) = H4_g_outer (H4_c_val k (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    have hval : H4_c_val k (2 * k + 1) = 2 * k + 1 - 2 * k := H4_c_val_leq k (2 * k + 1) (by omega)
    have h1 : 2 * k + 1 - 2 * k = 1 := by omega
    rw [h1] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H4_c_val ((k + 1 + j) + 1) (2 * k + 1) = H4_g_outer (H4_c_val (k + 1 + j) (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 2 - 2 * j = (2 * k + 2 - 2 * j - 2) + 2 := by omega
    have hc2 : H4_g_outer (2 * k + 2 - 2 * j) (2 * k + 1) = H4_g_outer ((2 * k + 2 - 2 * j - 2) + 2) (2 * k + 1) := congrArg (fun z => H4_g_outer z (2 * k + 1)) h_inner
    rw [hc2]
    rw [H4_g_outer_add_two]
    omega

lemma H4_c_val_diag_even (k : Nat) (hk : k > 0) : H4_c_val (2 * k) (2 * k) = 3 := by
  have H : H4_c_val (2 * k) (2 * k) = H4_c_val (k + 1 + (k - 1)) (2 * k) := by
    have h_eq : 2 * k = k + 1 + (k - 1) := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H4_even_phase2 k (k - 1) (by omega)
  have h_eq : 2 * k + 1 - 2 * (k - 1) = 3 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H4_c_val_diag_even_zero : H4_c_val 0 0 = 0 := by rfl

lemma H4_c_val_diag_odd (k : Nat) : H4_c_val (2 * k + 1) (2 * k + 1) = 2 := by
  have H : H4_c_val (2 * k + 1) (2 * k + 1) = H4_c_val (k + 1 + k) (2 * k + 1) := by
    have h_eq : 2 * k + 1 = k + 1 + k := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H4_odd_phase2 k k (by omega)
  have h_eq : 2 * k + 2 - 2 * k = 2 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H4_c_val_diag_pos (x : Nat) : H4_c_val (x + 1) (x + 1) > 0 := by
  have h_cases : (∃ k, x + 1 = 2 * k) ∨ (∃ k, x + 1 = 2 * k + 1) := by
    have hm : (x + 1) % 2 = 0 ∨ (x + 1) % 2 = 1 := by omega
    cases hm with
    | inl h0 =>
      left
      use ((x + 1) / 2)
      omega
    | inr h1 =>
      right
      use ((x + 1) / 2)
      omega
  cases h_cases with
  | inl he =>
    rcases he with ⟨k, hk⟩
    have hk_pos : k > 0 := by omega
    have h_val := H4_c_val_diag_even k hk_pos
    rw [hk]
    rw [h_val]
    exact by decide
  | inr ho =>
    rcases ho with ⟨k, hk⟩
    have h_val := H4_c_val_diag_odd k
    rw [hk]
    rw [h_val]
    exact by decide

lemma H4_c_step (x y : Nat) : evalPRF H4_c (mk_args2 (x + 1) y) = evalPRF H4_h (mk_args3 x (evalPRF H4_c (mk_args2 x y)) y) := by
  cases x with
  | zero => rfl
  | succ x => rfl

lemma H4_h_eq (m acc y : Nat) : evalPRF H4_h (mk_args3 m acc y) = H4_g_outer acc y := by
  induction m with
  | zero =>
    change (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 acc y)) = H4_g_outer acc y
    induction acc with
    | zero => rfl
    | succ a ih_a =>
      change (evalPRF (PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)) (mk_args3 a (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 a y)) y)) = H4_g_outer (a + 1) y
      induction a with
      | zero => rfl
      | succ a' ih_a' => rfl
  | succ m ih =>
    change evalPRF H4_h (mk_args3 m acc y) = H4_g_outer acc y
    exact ih

lemma H4_c_val_eq (x y : Nat) : evalPRF H4_c (mk_args2 x y) = H4_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have step : evalPRF H4_c (mk_args2 (x + 1) y) = evalPRF H4_h (mk_args3 x (evalPRF H4_c (mk_args2 x y)) y) := H4_c_step x y
    have h_eq : evalPRF H4_h (mk_args3 x (evalPRF H4_c (mk_args2 x y)) y) = H4_g_outer (evalPRF H4_c (mk_args2 x y)) y := H4_h_eq x (evalPRF H4_c (mk_args2 x y)) y
    have h_step2 : H4_g_outer (evalPRF H4_c (mk_args2 x y)) y = H4_g_outer (H4_c_val x y) y := by rw [ih]
    have h_def : H4_g_outer (H4_c_val x y) y = H4_c_val (x + 1) y := by rfl
    exact Eq.trans step (Eq.trans h_eq (Eq.trans h_step2 h_def))

lemma H4_comp (x : Nat) : evalPRF holdout_4 (fun _ => x) = evalPRF H4_c (mk_args2 (x + 1) (x + 1)) := by
  change evalPRF H4_c (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H4_c (mk_args2 (x + 1) (x + 1))
  apply congrArg (evalPRF H4_c)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

-- Proof produced in ~25 minutes (adapted from Sub Cycle template)
theorem holdout_4_diverges : ∀ x, evalPRF holdout_4 (fun _ => x) > 0 := by
  intro x
  rw [H4_comp x]
  rw [H4_c_val_eq (x + 1) (x + 1)]
  exact H4_c_val_diag_pos x

-- Translating holdout 5
-- M(C(R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2))),S,P(1,1)))
def holdout_5 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

def H5_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H5_c : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H5_h

def H5_g_outer (u v : Nat) : Nat :=
  match u with
  | 0 => v + 1
  | 1 => v
  | u' + 2 => u'

def H5_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H5_g_outer (H5_c_val x' y) y

lemma H5_g_outer_add_two (u v : Nat) : H5_g_outer (u + 2) v = u := by rfl

lemma H5_c_val_leq (x y : Nat) (hx : x ≤ y / 2) : H5_c_val x y = y - 2 * x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have h1 : x ≤ y / 2 := by omega
    have h2 : H5_c_val x y = y - 2 * x := ih h1
    have h_c : H5_c_val (x + 1) y = H5_g_outer (H5_c_val x y) y := by rfl
    have h_c2 : H5_c_val (x + 1) y = H5_g_outer (y - 2 * x) y := Eq.trans h_c (congrArg (fun z => H5_g_outer z y) h2)
    have h3 : y - 2 * x = (y - 2 * x - 2) + 2 := by omega
    have h_c3 : H5_c_val (x + 1) y = H5_g_outer ((y - 2 * x - 2) + 2) y := Eq.trans h_c2 (congrArg (fun z => H5_g_outer z y) h3)
    have h_c4 : H5_c_val (x + 1) y = y - 2 * x - 2 := Eq.trans h_c3 (H5_g_outer_add_two (y - 2 * x - 2) y)
    have h_final : y - 2 * x - 2 = y - 2 * (x + 1) := by omega
    exact Eq.trans h_c4 h_final

lemma H5_even_phase2 (k j : Nat) (hj : j ≤ k) : H5_c_val (k + 1 + j) (2 * k) = 2 * k + 1 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H5_c_val (k + 1) (2 * k) = H5_g_outer (H5_c_val k (2 * k)) (2 * k) := by rfl
    rw [hc]
    have hval : H5_c_val k (2 * k) = 2 * k - 2 * k := H5_c_val_leq k (2 * k) (by omega)
    have h0 : 2 * k - 2 * k = 0 := by omega
    rw [h0] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H5_c_val ((k + 1 + j) + 1) (2 * k) = H5_g_outer (H5_c_val (k + 1 + j) (2 * k)) (2 * k) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 1 - 2 * j = (2 * k + 1 - 2 * j - 2) + 2 := by omega
    have hc2 : H5_g_outer (2 * k + 1 - 2 * j) (2 * k) = H5_g_outer ((2 * k + 1 - 2 * j - 2) + 2) (2 * k) := congrArg (fun z => H5_g_outer z (2 * k)) h_inner
    rw [hc2]
    rw [H5_g_outer_add_two]
    omega

lemma H5_odd_phase2 (k j : Nat) (hj : j ≤ k) : H5_c_val (k + 1 + j) (2 * k + 1) = 2 * k + 1 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H5_c_val (k + 1) (2 * k + 1) = H5_g_outer (H5_c_val k (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    have hval : H5_c_val k (2 * k + 1) = 2 * k + 1 - 2 * k := H5_c_val_leq k (2 * k + 1) (by omega)
    have h1 : 2 * k + 1 - 2 * k = 1 := by omega
    rw [h1] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H5_c_val ((k + 1 + j) + 1) (2 * k + 1) = H5_g_outer (H5_c_val (k + 1 + j) (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 1 - 2 * j = (2 * k + 1 - 2 * j - 2) + 2 := by omega
    have hc2 : H5_g_outer (2 * k + 1 - 2 * j) (2 * k + 1) = H5_g_outer ((2 * k + 1 - 2 * j - 2) + 2) (2 * k + 1) := congrArg (fun z => H5_g_outer z (2 * k + 1)) h_inner
    rw [hc2]
    rw [H5_g_outer_add_two]
    omega

lemma H5_c_val_diag_even (k : Nat) : H5_c_val (2 * k + 1) (2 * k) = 1 := by
  have H : H5_c_val (2 * k + 1) (2 * k) = H5_c_val (k + 1 + k) (2 * k) := by
    have h_eq : 2 * k + 1 = k + 1 + k := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H5_even_phase2 k k (by omega)
  have h_eq : 2 * k + 1 - 2 * k = 1 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H5_c_val_diag_odd (k : Nat) : H5_c_val (2 * k + 2) (2 * k + 1) = 2 * k + 1 := by
  have H : H5_c_val (2 * k + 2) (2 * k + 1) = H5_g_outer (H5_c_val (2 * k + 1) (2 * k + 1)) (2 * k + 1) := by rfl
  rw [H]
  have H2 : H5_c_val (2 * k + 1) (2 * k + 1) = H5_c_val (k + 1 + k) (2 * k + 1) := by
    have h_eq : 2 * k + 1 = k + 1 + k := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H2]
  have h_val := H5_odd_phase2 k k (by omega)
  have h_eq : 2 * k + 1 - 2 * k = 1 := by omega
  rw [h_eq] at h_val
  rw [h_val]
  rfl

lemma H5_c_val_diag_pos (y : Nat) : H5_c_val (y + 1) y > 0 := by
  have h_cases : (∃ k, y = 2 * k) ∨ (∃ k, y = 2 * k + 1) := by
    have hm : y % 2 = 0 ∨ y % 2 = 1 := by omega
    cases hm with
    | inl h0 =>
      left
      use (y / 2)
      omega
    | inr h1 =>
      right
      use (y / 2)
      omega
  cases h_cases with
  | inl he =>
    rcases he with ⟨k, hk⟩
    have h_val := H5_c_val_diag_even k
    rw [hk]
    rw [h_val]
    exact by decide
  | inr ho =>
    rcases ho with ⟨k, hk⟩
    have h_val := H5_c_val_diag_odd k
    rw [hk]
    have H2 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    rw [H2]
    rw [h_val]
    omega

lemma H5_c_step (x y : Nat) : evalPRF H5_c (mk_args2 (x + 1) y) = evalPRF H5_h (mk_args3 x (evalPRF H5_c (mk_args2 x y)) y) := by
  cases x with
  | zero => rfl
  | succ x => rfl

lemma H5_h_eq (m acc y : Nat) : evalPRF H5_h (mk_args3 m acc y) = H5_g_outer acc y := by
  induction m with
  | zero =>
    change (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 acc y)) = H5_g_outer acc y
    induction acc with
    | zero => rfl
    | succ a ih_a =>
      change (evalPRF (PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)) (mk_args3 a (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 a y)) y)) = H5_g_outer (a + 1) y
      induction a with
      | zero => rfl
      | succ a' ih_a' => rfl
  | succ m ih =>
    change evalPRF H5_h (mk_args3 m acc y) = H5_g_outer acc y
    exact ih

lemma H5_c_val_eq (x y : Nat) : evalPRF H5_c (mk_args2 x y) = H5_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have step : evalPRF H5_c (mk_args2 (x + 1) y) = evalPRF H5_h (mk_args3 x (evalPRF H5_c (mk_args2 x y)) y) := H5_c_step x y
    have h_eq : evalPRF H5_h (mk_args3 x (evalPRF H5_c (mk_args2 x y)) y) = H5_g_outer (evalPRF H5_c (mk_args2 x y)) y := H5_h_eq x (evalPRF H5_c (mk_args2 x y)) y
    have h_step2 : H5_g_outer (evalPRF H5_c (mk_args2 x y)) y = H5_g_outer (H5_c_val x y) y := by rw [ih]
    have h_def : H5_g_outer (H5_c_val x y) y = H5_c_val (x + 1) y := by rfl
    exact Eq.trans step (Eq.trans h_eq (Eq.trans h_step2 h_def))

lemma H5_comp (x : Nat) : evalPRF holdout_5 (fun _ => x) = evalPRF H5_c (mk_args2 (x + 1) x) := by
  change evalPRF H5_c (fun j => evalPRFList prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H5_c (mk_args2 (x + 1) x)
  apply congrArg (evalPRF H5_c)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

-- Proof produced in ~15 minutes (adapted from Sub Cycle template)
theorem holdout_5_diverges : ∀ x, evalPRF holdout_5 (fun _ => x) > 0 := by
  intro x
  rw [H5_comp x]
  rw [H5_c_val_eq (x + 1) x]
  exact H5_c_val_diag_pos x

-- Translating holdout 6
-- M(C(R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2))),S,S))
def holdout_6 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

def H6_h : PRF 3 := PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))
def H6_c : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H6_h

def H6_g_outer (u v : Nat) : Nat :=
  match u with
  | 0 => v + 1
  | 1 => v
  | u' + 2 => u'

def H6_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H6_g_outer (H6_c_val x' y) y

lemma H6_g_outer_add_two (u v : Nat) : H6_g_outer (u + 2) v = u := by rfl

lemma H6_c_val_leq (x y : Nat) (hx : x ≤ y / 2) : H6_c_val x y = y - 2 * x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have h1 : x ≤ y / 2 := by omega
    have h2 : H6_c_val x y = y - 2 * x := ih h1
    have h_c : H6_c_val (x + 1) y = H6_g_outer (H6_c_val x y) y := by rfl
    have h_c2 : H6_c_val (x + 1) y = H6_g_outer (y - 2 * x) y := Eq.trans h_c (congrArg (fun z => H6_g_outer z y) h2)
    have h3 : y - 2 * x = (y - 2 * x - 2) + 2 := by omega
    have h_c3 : H6_c_val (x + 1) y = H6_g_outer ((y - 2 * x - 2) + 2) y := Eq.trans h_c2 (congrArg (fun z => H6_g_outer z y) h3)
    have h_c4 : H6_c_val (x + 1) y = y - 2 * x - 2 := Eq.trans h_c3 (H6_g_outer_add_two (y - 2 * x - 2) y)
    have h_final : y - 2 * x - 2 = y - 2 * (x + 1) := by omega
    exact Eq.trans h_c4 h_final

lemma H6_even_phase2 (k j : Nat) (hj : j ≤ k) : H6_c_val (k + 1 + j) (2 * k) = 2 * k + 1 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H6_c_val (k + 1) (2 * k) = H6_g_outer (H6_c_val k (2 * k)) (2 * k) := by rfl
    rw [hc]
    have hval : H6_c_val k (2 * k) = 2 * k - 2 * k := H6_c_val_leq k (2 * k) (by omega)
    have h0 : 2 * k - 2 * k = 0 := by omega
    rw [h0] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H6_c_val ((k + 1 + j) + 1) (2 * k) = H6_g_outer (H6_c_val (k + 1 + j) (2 * k)) (2 * k) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 1 - 2 * j = (2 * k + 1 - 2 * j - 2) + 2 := by omega
    have hc2 : H6_g_outer (2 * k + 1 - 2 * j) (2 * k) = H6_g_outer ((2 * k + 1 - 2 * j - 2) + 2) (2 * k) := congrArg (fun z => H6_g_outer z (2 * k)) h_inner
    rw [hc2]
    rw [H6_g_outer_add_two]
    omega

lemma H6_odd_phase2 (k j : Nat) (hj : j ≤ k) : H6_c_val (k + 1 + j) (2 * k + 1) = 2 * k + 1 - 2 * j := by
  induction j with
  | zero =>
    have ht : k + 1 + 0 = k + 1 := by omega
    rw [ht]
    have hc : H6_c_val (k + 1) (2 * k + 1) = H6_g_outer (H6_c_val k (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    have hval : H6_c_val k (2 * k + 1) = 2 * k + 1 - 2 * k := H6_c_val_leq k (2 * k + 1) (by omega)
    have h1 : 2 * k + 1 - 2 * k = 1 := by omega
    rw [h1] at hval
    rw [hval]
    rfl
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have h_ih := ih hj'
    have h1 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [h1]
    have hc : H6_c_val ((k + 1 + j) + 1) (2 * k + 1) = H6_g_outer (H6_c_val (k + 1 + j) (2 * k + 1)) (2 * k + 1) := by rfl
    rw [hc]
    rw [h_ih]
    have h_inner : 2 * k + 1 - 2 * j = (2 * k + 1 - 2 * j - 2) + 2 := by omega
    have hc2 : H6_g_outer (2 * k + 1 - 2 * j) (2 * k + 1) = H6_g_outer ((2 * k + 1 - 2 * j - 2) + 2) (2 * k + 1) := congrArg (fun z => H6_g_outer z (2 * k + 1)) h_inner
    rw [hc2]
    rw [H6_g_outer_add_two]
    omega

lemma H6_c_val_diag_even (k : Nat) (hk : k > 0) : H6_c_val (2 * k) (2 * k) = 3 := by
  have H : H6_c_val (2 * k) (2 * k) = H6_c_val (k + 1 + (k - 1)) (2 * k) := by
    have h_eq : 2 * k = k + 1 + (k - 1) := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H6_even_phase2 k (k - 1) (by omega)
  have h_eq : 2 * k + 1 - 2 * (k - 1) = 3 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H6_c_val_diag_odd (k : Nat) : H6_c_val (2 * k + 1) (2 * k + 1) = 1 := by
  have H : H6_c_val (2 * k + 1) (2 * k + 1) = H6_c_val (k + 1 + k) (2 * k + 1) := by
    have h_eq : 2 * k + 1 = k + 1 + k := by omega
    conv => lhs; arg 1; rw [h_eq]
  rw [H]
  have h_val := H6_odd_phase2 k k (by omega)
  have h_eq : 2 * k + 1 - 2 * k = 1 := by omega
  rw [h_eq] at h_val
  exact h_val

lemma H6_c_val_diag_pos (x : Nat) : H6_c_val (x + 1) (x + 1) > 0 := by
  have h_cases : (∃ k, x + 1 = 2 * k) ∨ (∃ k, x + 1 = 2 * k + 1) := by
    have hm : (x + 1) % 2 = 0 ∨ (x + 1) % 2 = 1 := by omega
    cases hm with
    | inl h0 =>
      left
      use ((x + 1) / 2)
      omega
    | inr h1 =>
      right
      use ((x + 1) / 2)
      omega
  cases h_cases with
  | inl he =>
    rcases he with ⟨k, hk⟩
    have hk_pos : k > 0 := by omega
    have h_val := H6_c_val_diag_even k hk_pos
    rw [hk]
    rw [h_val]
    exact by decide
  | inr ho =>
    rcases ho with ⟨k, hk⟩
    have h_val := H6_c_val_diag_odd k
    rw [hk]
    rw [h_val]
    exact by decide

lemma H6_c_step (x y : Nat) : evalPRF H6_c (mk_args2 (x + 1) y) = evalPRF H6_h (mk_args3 x (evalPRF H6_c (mk_args2 x y)) y) := by
  cases x with
  | zero => rfl
  | succ x => rfl

lemma H6_h_eq (m acc y : Nat) : evalPRF H6_h (mk_args3 m acc y) = H6_g_outer acc y := by
  induction m with
  | zero =>
    change (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 acc y)) = H6_g_outer acc y
    induction acc with
    | zero => rfl
    | succ a ih_a =>
      change (evalPRF (PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)) (mk_args3 a (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩))) (mk_args2 a y)) y)) = H6_g_outer (a + 1) y
      induction a with
      | zero => rfl
      | succ a' ih_a' => rfl
  | succ m ih =>
    change evalPRF H6_h (mk_args3 m acc y) = H6_g_outer acc y
    exact ih

lemma H6_c_val_eq (x y : Nat) : evalPRF H6_c (mk_args2 x y) = H6_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have step : evalPRF H6_c (mk_args2 (x + 1) y) = evalPRF H6_h (mk_args3 x (evalPRF H6_c (mk_args2 x y)) y) := H6_c_step x y
    have h_eq : evalPRF H6_h (mk_args3 x (evalPRF H6_c (mk_args2 x y)) y) = H6_g_outer (evalPRF H6_c (mk_args2 x y)) y := H6_h_eq x (evalPRF H6_c (mk_args2 x y)) y
    have h_step2 : H6_g_outer (evalPRF H6_c (mk_args2 x y)) y = H6_g_outer (H6_c_val x y) y := by rw [ih]
    have h_def : H6_g_outer (H6_c_val x y) y = H6_c_val (x + 1) y := by rfl
    exact Eq.trans step (Eq.trans h_eq (Eq.trans h_step2 h_def))

lemma H6_comp (x : Nat) : evalPRF holdout_6 (fun _ => x) = evalPRF H6_c (mk_args2 (x + 1) (x + 1)) := by
  change evalPRF H6_c (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H6_c (mk_args2 (x + 1) (x + 1))
  apply congrArg (evalPRF H6_c)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

-- Proof produced in ~10 minutes (adapted from Sub Cycle template)
theorem holdout_6_diverges : ∀ x, evalPRF holdout_6 (fun _ => x) > 0 := by
  intro x
  rw [H6_comp x]
  rw [H6_c_val_eq (x + 1) (x + 1)]
  exact H6_c_val_diag_pos x

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
