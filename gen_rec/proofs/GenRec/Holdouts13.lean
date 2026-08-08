
import GenRec.Syntax
import GenRec.Semantics



open GenRec

namespace Holdouts13


-- General
def mk_args2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
def mk_args3 (a b c : Nat) : Fin 3 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else c
def mk_args4 (a b c d : Nat) : Fin 4 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d
def mk_args5 (a b c d e : Nat) : Fin 5 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else if i.val = 3 then d else e


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

def H9_inner_inner_g : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H9_inner_inner : PRF 4 := PRF.primRec H9_inner_inner_g ((PRF.proj 5 ⟨1, by decide⟩))
def H9_inner : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) H9_inner_inner
def H9_c : PRF 2 := PRF.primRec (PRF.succ) H9_inner

lemma H9_comp (x : Nat) : evalPRF holdout_9 (fun _ => x) = evalPRF H9_c (mk_args2 x x) := by
  change evalPRF H9_c (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H9_c (mk_args2 x x)
  apply congrArg (evalPRF H9_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl

def H9_g (m y : Nat) : Nat :=
  match m with
  | 0 => y
  | m' + 1 => m'

def H9_inner_val (u v y : Nat) : Nat :=
  match u with
  | 0 => v
  | u' + 1 => H9_g (H9_inner_val u' v y) y

def H9_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H9_inner_val x' (H9_c_val x' y) y

lemma H9_g_eq (a b y : Nat) : evalPRF H9_inner_inner_g (mk_args3 a b y) = H9_g a y := by
  induction a with
  | zero =>
    change evalPRF (PRF.proj 2 ⟨1, by decide⟩) (mk_args2 b y) = y
    rfl
  | succ a ih =>
    change evalPRF (PRF.proj 4 ⟨0, by decide⟩) _ = a
    rfl

lemma H9_inner_inner_eq (u b a y : Nat) : evalPRF H9_inner_inner (mk_args4 u b a y) = H9_g b y := by
  induction u with
  | zero =>
    change evalPRF H9_inner_inner_g (mk_args3 b a y) = H9_g b y
    exact H9_g_eq b a y
  | succ u ih =>
    change evalPRF (PRF.proj 5 ⟨1, by decide⟩) _ = H9_g b y
    exact ih

lemma H9_inner_eq (u v y : Nat) : evalPRF H9_inner (mk_args3 u v y) = H9_inner_val u v y := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change evalPRF H9_inner_inner (mk_args4 u (evalPRF H9_inner (mk_args3 u v y)) v y) = H9_g (H9_inner_val u v y) y
    rw [H9_inner_inner_eq u (evalPRF H9_inner (mk_args3 u v y)) v y]
    rw [ih]

lemma H9_c_val_eq (x y : Nat) : evalPRF H9_c (mk_args2 x y) = H9_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF H9_inner (mk_args3 x (evalPRF H9_c (mk_args2 x y)) y) = H9_inner_val x (H9_c_val x y) y
    rw [H9_inner_eq x (evalPRF H9_c (mk_args2 x y)) y]
    rw [ih]

def H9_T : Nat → Nat
  | 0 => 0
  | x + 1 => H9_T x + x

lemma H9_g_mod (a y : Nat) : H9_g a y ≡ a + y [MOD y + 1] := by
  cases a with
  | zero =>
    change y ≡ 0 + y [MOD y + 1]
    have h : 0 + y = y := by omega
    rw [h]
  | succ a =>
    change a % (y + 1) = (a + 1 + y) % (y + 1)
    have h : a + 1 + y = a + (y + 1) := by omega
    rw [h]
    exact (Nat.add_mod_right a (y + 1)).symm

lemma H9_inner_val_mod (u v y : Nat) : H9_inner_val u v y ≡ v + u * y [MOD y + 1] := by
  induction u with
  | zero =>
    change v ≡ v + 0 * y [MOD y + 1]
    have h : v + 0 * y = v := by omega
    rw [h]
  | succ u ih =>
    change H9_g (H9_inner_val u v y) y ≡ v + (u + 1) * y [MOD y + 1]
    have h1 := H9_g_mod (H9_inner_val u v y) y
    have h2 : (H9_inner_val u v y) + y ≡ v + u * y + y [MOD y + 1] := Nat.ModEq.add_right y ih
    have h3 : v + u * y + y = v + (u + 1) * y := by ring
    rw [h3] at h2
    exact Nat.ModEq.trans h1 h2

lemma H9_c_val_mod (x y : Nat) : H9_c_val x y + H9_T x ≡ y + 1 [MOD y + 1] := by
  induction x with
  | zero =>
    change y + 1 + 0 ≡ y + 1 [MOD y + 1]
    have h : y + 1 + 0 = y + 1 := by omega
    rw [h]
  | succ x ih =>
    change H9_inner_val x (H9_c_val x y) y + (H9_T x + x) ≡ y + 1 [MOD y + 1]
    have h1 := H9_inner_val_mod x (H9_c_val x y) y
    have h2 : H9_inner_val x (H9_c_val x y) y + (H9_T x + x) ≡ H9_c_val x y + x * y + (H9_T x + x) [MOD y + 1] := Nat.ModEq.add_right (H9_T x + x) h1
    have h3 : H9_c_val x y + x * y + (H9_T x + x) = H9_c_val x y + H9_T x + x * (y + 1) := by ring
    rw [h3] at h2
    have h4 : H9_c_val x y + H9_T x + x * (y + 1) ≡ H9_c_val x y + H9_T x [MOD y + 1] := by
      change (H9_c_val x y + H9_T x + x * (y + 1)) % (y + 1) = (H9_c_val x y + H9_T x) % (y + 1)
      have h_mul : x * (y + 1) = (y + 1) * x := by ring
      rw [h_mul]
      exact Nat.add_mul_mod_self_left (H9_c_val x y + H9_T x) (y + 1) x
    have h5 := Nat.ModEq.trans h2 h4
    exact Nat.ModEq.trans h5 ih

lemma H9_T_val (x : Nat) : 2 * H9_T x + x = x * x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change 2 * (H9_T x + x) + (x + 1) = (x + 1) * (x + 1)
    have h1 : 2 * (H9_T x + x) + (x + 1) = (2 * H9_T x + x) + 2 * x + 1 := by ring
    rw [h1, ih]
    ring

lemma H9_c_val_diag_not_zero (x : Nat) : H9_c_val x x ≠ 0 := by
  cases x with
  | zero =>
--     change H9_c_val 0 0 ≠ 0
    change 1 ≠ 0
    intro h
    contradiction
  | succ x =>
    cases x with
    | zero =>
      change H9_c_val 1 1 ≠ 0
      change 2 ≠ 0
      intro h
      contradiction
    | succ x =>
      intro h
      have hmod : H9_c_val (x + 2) (x + 2) + H9_T (x + 2) ≡ x + 2 + 1 [MOD x + 2 + 1] := H9_c_val_mod (x + 2) (x + 2)
      rw [h] at hmod
      have hmod2 : H9_T (x + 2) ≡ 0 [MOD x + 3] := by
        have hz : 0 + H9_T (x + 2) = H9_T (x + 2) := by omega
        rw [hz] at hmod
        change H9_T (x + 2) % (x + 3) = (x + 3) % (x + 3) at hmod
        have h_mod_self : (x + 3) % (x + 3) = 0 := Nat.mod_self (x + 3)
        rw [h_mod_self] at hmod
        exact hmod
      have h_dvd : (x + 3) ∣ H9_T (x + 2) := Nat.dvd_of_mod_eq_zero hmod2
      rcases h_dvd with ⟨q, hq⟩
      have hq2 : H9_T (x + 2) = q * (x + 3) := by
        rw [hq, Nat.mul_comm]
      have htval : 2 * H9_T (x + 2) + (x + 2) = (x + 2) * (x + 2) := H9_T_val (x + 2)
      rw [hq2] at htval
      -- We have 2 * (q * (x + 3)) + (x + 2) = (x + 2) * (x + 2)
      have h1 : 2 * (q * (x + 3)) + 2 * (x + 3) = (x + 2) * (x + 3) + 2 := by
        have h_add : 2 * (q * (x + 3)) + (x + 2) + (x + 4) = (x + 2) * (x + 2) + (x + 4) := by omega
        have hl : 2 * (q * (x + 3)) + (x + 2) + (x + 4) = 2 * (q * (x + 3)) + 2 * (x + 3) := by ring
        have hr : (x + 2) * (x + 2) + (x + 4) = (x + 2) * (x + 3) + 2 := by ring
        rw [hl, hr] at h_add
        exact h_add
      have h2 : 2 * (q * (x + 3)) + 2 * (x + 3) = (2 * q + 2) * (x + 3) := by ring
      rw [h2] at h1
      have h3 : (2 * q + 2) * (x + 3) - (x + 2) * (x + 3) = 2 := by omega
      have h4 : (2 * q + 2) * (x + 3) - (x + 2) * (x + 3) = (2 * q + 2 - (x + 2)) * (x + 3) := by
        rw [Nat.sub_mul]
      rw [h4] at h3
      cases h_A : (2 * q + 2 - (x + 2)) with
      | zero =>
        rw [h_A] at h3
        have h0 : 0 * (x + 3) = 0 := by ring
        rw [h0] at h3
        contradiction
      | succ A' =>
        rw [h_A] at h3
        cases A' with
        | zero =>
          have hz : (0 + 1) * (x + 3) = x + 3 := by ring
          rw [hz] at h3
          omega
        | succ A'' =>
          have hs : (A'' + 2) * (x + 3) = (A'' + 2) * (x + 2) + A'' + 2 := by ring
          rw [hs] at h3
          have hx_cases : x + 2 = (x + 2 - 2) + 2 := by omega
          have he : (A'' + 2) * ((x + 2 - 2) + 2) + A'' + 2 = (A'' + 2) * (x + 2 - 2) + 3 * A'' + 6 := by ring
          rw [hx_cases, he] at h3
          omega

-- Proof produced in ~25 minutes (adapted from Poly Div template)
theorem holdout_9_diverges : ∀ x, evalPRF holdout_9 (fun _ => x) > 0 := by
  intro x
  rw [H9_comp x]
  rw [H9_c_val_eq x x]
  have h_not_zero : H9_c_val x x ≠ 0 := H9_c_val_diag_not_zero x
  omega

-- Translating holdout 10
-- M(C(R(S,R(P(2,1),R(R(P(2,2),P(4,1)),P(5,2)))),S,S))
def holdout_10 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) ((PRF.proj 5 ⟨1, by decide⟩))))) prf_list![PRF.succ, PRF.succ]

lemma H10_comp (x : Nat) : evalPRF holdout_10 (fun _ => x) = evalPRF H9_c (mk_args2 (x + 1) (x + 1)) := by
  change evalPRF H9_c (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H9_c (mk_args2 (x + 1) (x + 1))
  apply congrArg (evalPRF H9_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl

-- Proof produced in ~5 minutes (adapted from holdout 9)
theorem holdout_10_diverges : ∀ x, evalPRF holdout_10 (fun _ => x) > 0 := by
  intro x
  rw [H10_comp x]
  rw [H9_c_val_eq (x + 1) (x + 1)]
  have h_not_zero : H9_c_val (x + 1) (x + 1) ≠ 0 := H9_c_val_diag_not_zero (x + 1)
  omega
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

lemma H13_comp (x : Nat) : evalPRF holdout_13 (fun _ => x) = evalPRF H11_c (mk_args2 (x + 1) x) := by
  change evalPRF H11_c (fun j => evalPRFList prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H11_c (mk_args2 (x + 1) x)
  apply congrArg (evalPRF H11_c); funext ⟨val, isLt⟩; match val with | 0 => rfl | 1 => rfl

def H13_step (v acc _ : Nat) : Nat :=
  match v with
  | 0 => acc
  | v'' + 1 => v''

def H13_g (v y : Nat) : Nat :=
  match v with
  | 0 => y + 1
  | 1 => y + 1
  | v' + 2 => v'

def H13_c_val (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H13_g (H13_c_val x' y) y

lemma H13_step_eq (v acc y : Nat) : evalPRF (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) (mk_args3 v acc y) = H13_step v acc y := by
  induction v with
  | zero => rfl
  | succ v ih => rfl

lemma H13_g_succ (v y : Nat) : H13_step v (H13_g v y) y = H13_g (v + 1) y := by
  cases v with
  | zero => rfl
  | succ v' => rfl

lemma H13_g_eq (v y : Nat) : evalPRF (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) (mk_args2 v y) = H13_g v y := by
  induction v with
  | zero => rfl
  | succ v ih =>
    change evalPRF (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) (mk_args3 v (evalPRF (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) (mk_args2 v y)) y) = H13_g (v + 1) y
    rw [H13_step_eq]
    rw [ih]
    rw [H13_g_succ]

lemma H13_h_eq (u v y : Nat) : evalPRF H11_h (mk_args3 u v y) = H13_g v y := by
  induction u with
  | zero =>
    exact H13_g_eq v y
  | succ u ih =>
    change evalPRF (PRF.proj 4 ⟨1, by decide⟩) _ = H13_g v y
    exact ih

lemma H13_c_val_eq (x y : Nat) : evalPRF H11_c (mk_args2 x y) = H13_c_val x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF H11_h (mk_args3 x (evalPRF H11_c (mk_args2 x y)) y) = H13_c_val (x + 1) y
    rw [H13_h_eq]
    rw [ih]
    rfl

def seq_even (k x : Nat) : Nat := 2 * k + 1 - 2 * (x % (k + 1))
def seq_odd (k x : Nat) : Nat := 2 * k + 2 - 2 * (x % (k + 2))

lemma my_mod_helper {x m q c : Nat} (h : x = q * m + c) (hc : c < m) : x % m = c := by
  rw [h, Nat.add_comm (q * m) c, Nat.mul_comm q m, Nat.add_mul_mod_self_left c m q, Nat.mod_eq_of_lt hc]

lemma mod_add_one_eq_zero_of_eq {x k : Nat} (h : x % (k + 1) = k) : (x + 1) % (k + 1) = 0 := by
  have h1 := Nat.div_add_mod x (k + 1)
  have h2 : x + 1 = (x / (k + 1) + 1) * (k + 1) + 0 := by
    calc x + 1 = ((k + 1) * (x / (k + 1)) + x % (k + 1)) + 1 := by rw [h1]
         _ = ((k + 1) * (x / (k + 1)) + k) + 1 := by rw [h]
         _ = (k + 1) * (x / (k + 1)) + (k + 1) := by ring
         _ = (x / (k + 1) + 1) * (k + 1) + 0 := by ring
  exact my_mod_helper h2 (by omega)

lemma mod_add_one_eq_succ_of_lt {x k : Nat} (h : x % (k + 1) < k) : (x + 1) % (k + 1) = x % (k + 1) + 1 := by
  have h1 := Nat.div_add_mod x (k + 1)
  have h2 : x + 1 = (x / (k + 1)) * (k + 1) + (x % (k + 1) + 1) := by
    calc x + 1 = ((k + 1) * (x / (k + 1)) + x % (k + 1)) + 1 := by rw [h1]
         _ = (x / (k + 1)) * (k + 1) + (x % (k + 1) + 1) := by ring
  exact my_mod_helper h2 (by omega)

lemma H13_even_val (k x : Nat) : H13_c_val x (2 * k) = seq_even k x := by
  induction x with
  | zero =>
    change 2 * k + 1 = 2 * k + 1 - 2 * (0 % (k + 1))
    rw [Nat.zero_mod]
    omega
  | succ x ih =>
    change H13_g (H13_c_val x (2 * k)) (2 * k) = seq_even k (x + 1)
    rw [ih]
    have h_mod_lt : x % (k + 1) < k + 1 := Nat.mod_lt x (by omega)
    have h_cases : x % (k + 1) = k ∨ x % (k + 1) < k := by omega
    cases h_cases with
    | inl h1 =>
      have h2 : (x + 1) % (k + 1) = 0 := mod_add_one_eq_zero_of_eq h1
      unfold seq_even
      rw [h1, h2]
      have h3 : 2 * k + 1 - 2 * k = 1 := by omega
      rw [h3]
      change H13_g 1 (2 * k) = 2 * k + 1 - 2 * 0
      rfl
    | inr h1 =>
      have h2 : (x + 1) % (k + 1) = x % (k + 1) + 1 := mod_add_one_eq_succ_of_lt h1
      unfold seq_even
      rw [h2]
      have h_val : 2 * k + 1 - 2 * (x % (k + 1)) = (2 * k + 1 - 2 * (x % (k + 1)) - 2) + 2 := by omega
      rw [h_val]
      change H13_g ((2 * k + 1 - 2 * (x % (k + 1)) - 2) + 2) (2 * k) = 2 * k + 1 - 2 * (x % (k + 1) + 1)
      change 2 * k + 1 - 2 * (x % (k + 1)) - 2 = 2 * k + 1 - 2 * (x % (k + 1) + 1)
      omega

lemma H13_odd_val (k x : Nat) : H13_c_val x (2 * k + 1) = seq_odd k x := by
  induction x with
  | zero =>
    change (2 * k + 1) + 1 = 2 * k + 2 - 2 * (0 % (k + 2))
    rw [Nat.zero_mod]
    omega
  | succ x ih =>
    change H13_g (H13_c_val x (2 * k + 1)) (2 * k + 1) = seq_odd k (x + 1)
    rw [ih]
    have h_mod_lt : x % (k + 2) < k + 2 := Nat.mod_lt x (by omega)
    have h_cases : x % (k + 2) = k + 1 ∨ x % (k + 2) < k + 1 := by omega
    cases h_cases with
    | inl h1 =>
      have h2 : (x + 1) % (k + 2) = 0 := mod_add_one_eq_zero_of_eq h1
      unfold seq_odd
      rw [h1, h2]
      have h3 : 2 * k + 2 - 2 * (k + 1) = 0 := by omega
      rw [h3]
      change H13_g 0 (2 * k + 1) = 2 * k + 2 - 2 * 0
      rfl
    | inr h1 =>
      have h2 : (x + 1) % (k + 2) = x % (k + 2) + 1 := mod_add_one_eq_succ_of_lt h1
      unfold seq_odd
      rw [h2]
      have h_cases2 : x % (k + 2) = k ∨ x % (k + 2) < k := by omega
      cases h_cases2 with
      | inl h3 =>
        rw [h3]
        have h4 : 2 * k + 2 - 2 * k = 2 := by omega
        rw [h4]
        change H13_g 2 (2 * k + 1) = 2 * k + 2 - 2 * (k + 1)
        have h5 : 2 * k + 2 - 2 * (k + 1) = 0 := by omega
        rw [h5]
        rfl
      | inr h3 =>
        have h_val : 2 * k + 2 - 2 * (x % (k + 2)) = (2 * k + 2 - 2 * (x % (k + 2)) - 2) + 2 := by omega
        rw [h_val]
        change H13_g ((2 * k + 2 - 2 * (x % (k + 2)) - 2) + 2) (2 * k + 1) = 2 * k + 2 - 2 * (x % (k + 2) + 1)
        change 2 * k + 2 - 2 * (x % (k + 2)) - 2 = 2 * k + 2 - 2 * (x % (k + 2) + 1)
        omega

-- Proof produced in ~20 minutes (adapted from structural cases)
theorem holdout_13_diverges : ∀ x, evalPRF holdout_13 (fun _ => x) > 0 := by
  intro x
  rw [H13_comp x]
  rw [H13_c_val_eq (x + 1) x]
  have h_cases : (∃ k, x = 2 * k) ∨ (∃ k, x = 2 * k + 1) := by
    have h1 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    cases h1 with
    | inl h2 =>
      left
      use x / 2
      have h3 := Nat.div_add_mod x 2
      omega
    | inr h2 =>
      right
      use x / 2
      have h3 := Nat.div_add_mod x 2
      omega
  cases h_cases with
  | inl h1 =>
    rcases h1 with ⟨k, hk⟩
    rw [hk]
    rw [H13_even_val]
    unfold seq_even
    have h_mod_lt : (2 * k + 1) % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
    have h2 : 2 * k + 1 = 1 * (k + 1) + k := by ring
    have h_mod_val : (2 * k + 1) % (k + 1) = k := my_mod_helper h2 (by omega)
    rw [h_mod_val]
    omega
  | inr h1 =>
    rcases h1 with ⟨k, hk⟩
    rw [hk]
    rw [H13_odd_val]
    unfold seq_odd
    have h2 : 2 * k + 2 = 1 * (k + 2) + k := by ring
    have h_mod_val : (2 * k + 2) % (k + 2) = k := my_mod_helper h2 (by omega)
    rw [h_mod_val]
    omega

-- Translating holdout 14
-- M(R(C(S,Z0),R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1)))))
def holdout_14 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H14_f (u x : Nat) : Nat :=
  match u with
  | 0 => x
  | u' + 1 => u'

def H14_h (u x : Nat) : Nat :=
  match u with
  | 0 => x + 1
  | u' + 1 => H14_f (H14_h u' x) u'

def H14_val (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x' + 1 => H14_h x' (H14_val x')

lemma H14_f_eq (u x _acc : Nat) : evalPRF (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) (mk_args2 u x) = H14_f u x := by
  induction u with
  | zero => rfl
  | succ u ih => rfl

lemma H14_h_inner_eq (v u x : Nat) : evalPRF (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]) (mk_args3 u v x) = H14_f v u := by
  change evalPRF (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) (mk_args2 v u) = H14_f v u
  rw [H14_f_eq v u x]

lemma H14_h_eq (u x : Nat) : evalPRF (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) (mk_args2 u x) = H14_h u x := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change evalPRF (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]) (mk_args3 u (evalPRF (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) (mk_args2 u x)) x) = H14_h (u + 1) x
    rw [H14_h_inner_eq]
    rw [ih]
    rfl

lemma H14_val_eq (x : Nat) : evalPRF holdout_14 (fun _ => x) = H14_val x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) (mk_args2 x (evalPRF holdout_14 (fun _ => x))) = H14_val (x + 1)
    rw [H14_h_eq]
    rw [ih]
    rfl

lemma H14_h_le (u y : Nat) (h : u ≤ y + 1) : H14_h u y = y + 1 - u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change H14_f (H14_h u y) u = y + 1 - (u + 1)
    have h1 : u ≤ y + 1 := by omega
    rw [ih h1]
    have h2 : y + 1 - u = (y + 1 - (u + 1)) + 1 := by omega
    have h3 : y + 1 - (u + 1) + 1 = (y + 1 - (u + 1)) + 1 := by rfl
    rw [h2]
    change H14_f ((y + 1 - (u + 1)) + 1) u = y + 1 - (u + 1)
    rfl

lemma H14_h_y_plus_2 (y : Nat) : H14_h (y + 2) y = y + 1 := by
  change H14_f (H14_h (y + 1) y) (y + 1) = y + 1
  have h1 : y + 1 ≤ y + 1 := by omega
  rw [H14_h_le (y + 1) y h1]
  have h2 : y + 1 - (y + 1) = 0 := by omega
  rw [h2]
  rfl

lemma H14_val_eq_sub_2 (x : Nat) (h : x ≥ 4) : H14_val x = x - 2 := by
  induction x, h using Nat.le_induction with
  | base => rfl
  | succ x hx ih =>
    change H14_h x (H14_val x) = x + 1 - 2
    rw [ih]
    have h1 : (x - 2) + 2 = x := by omega
    have h2 : H14_h x (x - 2) = H14_h ((x - 2) + 2) (x - 2) := by rw [h1]
    rw [h2]
    rw [H14_h_y_plus_2 (x - 2)]
    omega

-- Proof produced in ~20 minutes (new Induction template)
theorem holdout_14_diverges : ∀ x, evalPRF holdout_14 (fun _ => x) > 0 := by
  intro x
  rw [H14_val_eq x]
  have h_cases : x < 4 ∨ x ≥ 4 := by omega
  cases h_cases with
  | inl h1 =>
    -- Finite check for x < 4
    have h2 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    rcases h2 with h3 | h3 | h3 | h3
    · rw [h3]; decide
    · rw [h3]; decide
    · rw [h3]; decide
    · rw [h3]; decide
  | inr h1 =>
    rw [H14_val_eq_sub_2 x h1]
    omega

end Holdouts13
