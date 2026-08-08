import GenRec.Syntax
import GenRec.Semantics

open GenRec

namespace Holdouts14

def mk_args2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
def mk_args3 (a b c : Nat) : Fin 3 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else c


-- Translating holdout 0
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_0 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_0_diverges : ∀ x, evalPRF holdout_0 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 1
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_1 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_1_diverges : ∀ x, evalPRF holdout_1 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 2
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),P(1,1)))
def holdout_2 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_2_diverges : ∀ x, evalPRF holdout_2 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 3
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_3 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_3_diverges : ∀ x, evalPRF holdout_3 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 4
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),P(1,1)))
def holdout_4 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_4_diverges : ∀ x, evalPRF holdout_4 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 5
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_5 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_5_diverges : ∀ x, evalPRF holdout_5 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 6
-- M(C(R(P(2,1),R(P(3,1),R(R(P(3,3),P(5,1)),P(6,2)))),P(1,1),S,P(1,1)))
def holdout_6 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 3 ⟨2, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩))) ((PRF.proj 6 ⟨1, by decide⟩))))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_6_diverges : ∀ x, evalPRF holdout_6 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 7
-- M(C(R(P(2,1),R(R(P(2,1),R(P(3,3),P(5,1))),P(5,2))),S,S,S))
def holdout_7 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨2, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, PRF.succ]

theorem holdout_7_diverges : ∀ x, evalPRF holdout_7 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 8
-- M(C(R(P(2,1),R(R(P(2,2),R(Z3,P(5,1))),P(5,2))),S,P(1,1),S))
def holdout_8 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec (PRF.zero 3) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_8_diverges : ∀ x, evalPRF holdout_8 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 9
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,1),P(5,1))),P(5,2))),S,S,S))
def holdout_9 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨0, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, PRF.succ]

theorem holdout_9_diverges : ∀ x, evalPRF holdout_9 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 10
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,P(1,1),S))
def holdout_10 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨1, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_10_diverges : ∀ x, evalPRF holdout_10 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 11
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,S,P(1,1)))
def holdout_11 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨1, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_11_diverges : ∀ x, evalPRF holdout_11 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 12
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,S,S))
def holdout_12 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨1, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, PRF.succ]

theorem holdout_12_diverges : ∀ x, evalPRF holdout_12 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 13
-- M(C(R(Z1,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_13 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_13_diverges : ∀ x, evalPRF holdout_13 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 14
-- M(C(R(Z1,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,P(1,1)))
def holdout_14 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_14_diverges : ∀ x, evalPRF holdout_14 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 15
-- M(C(R(Z1,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_15 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_15_diverges : ∀ x, evalPRF holdout_15 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 16
-- M(C(R(Z1,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def holdout_16 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_16_diverges : ∀ x, evalPRF holdout_16 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 17
-- M(C(R(Z1,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),S,S))
def holdout_17 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_17_diverges : ∀ x, evalPRF holdout_17 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 18
-- M(C(R(Z1,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_18 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_18_diverges : ∀ x, evalPRF holdout_18 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 19
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),S,S))
def holdout_19 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_19_diverges : ∀ x, evalPRF holdout_19 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 20
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def holdout_20 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_20_diverges : ∀ x, evalPRF holdout_20 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 21
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_21 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_21_diverges : ∀ x, evalPRF holdout_21 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 22
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_22 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_22_diverges : ∀ x, evalPRF holdout_22 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 23
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_23 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H23_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H23_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H23_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H23_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H23_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H23_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H23_a (H23_c x' y) (H23_b x' (H23_c x' y) y)

lemma H23_a_val (x y : Nat) : evalPRF H23_a_prf (mk_args2 x y) = H23_a x y := by
  induction x <;> rfl

lemma H23_b_val (x acc y : Nat) : evalPRF H23_b_prf (mk_args3 x acc y) = H23_b x acc y := by
  induction x <;> rfl

lemma H23_c_val (x y : Nat) : evalPRF H23_c_prf (mk_args2 x y) = H23_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H23_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H23_b_prf]) (mk_args3 x (evalPRF H23_c_prf (mk_args2 x y)) y) = H23_c (x + 1) y
    rw [ih]
    change evalPRF H23_a_prf (mk_args2 (H23_c x y) (evalPRF H23_b_prf (mk_args3 x (H23_c x y) y))) = H23_a (H23_c x y) (H23_b x (H23_c x y) y)
    rw [H23_b_val, H23_a_val]

lemma H23_c_cf (x y : Nat) (h : x < y + 0) (hx : x > 0) : H23_c x y = y + 0 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H23_a (H23_c x y) (H23_b x (H23_c x y) y) = y + 0 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      have hy : y > 0 := by omega
      have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      rfl
    | inr hpos =>
      have h1 : x < y + 0 := by omega
      rw [ih h1 hpos]
      have h2 : y + 0 - x > 0 := by omega
      have h3 : ∃ k, y + 0 - x = k + 1 := by use (y + 0 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H23_a (k + 1) (H23_b x (k + 1) y) = y + 0 - (x + 1)
      change k = y + 0 - (x + 1)
      omega

lemma H23_comp (x : Nat) : evalPRF holdout_23 (fun _ => x) = evalPRF H23_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H23_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H23_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H23_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_23_diverges : ∀ x, evalPRF holdout_23 (fun _ => x) > 0 := by
  intro x
  rw [H23_comp x]
  cases x with
  | zero =>
    rw [H23_c_val]
    decide
  | succ x' =>
    rw [H23_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 0 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H23_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 24
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_24 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H24_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H24_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H24_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H24_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H24_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H24_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H24_a (H24_c x' y) (H24_b x' (H24_c x' y) y)

lemma H24_a_val (x y : Nat) : evalPRF H24_a_prf (mk_args2 x y) = H24_a x y := by
  induction x <;> rfl

lemma H24_b_val (x acc y : Nat) : evalPRF H24_b_prf (mk_args3 x acc y) = H24_b x acc y := by
  induction x <;> rfl

lemma H24_c_val (x y : Nat) : evalPRF H24_c_prf (mk_args2 x y) = H24_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H24_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H24_b_prf]) (mk_args3 x (evalPRF H24_c_prf (mk_args2 x y)) y) = H24_c (x + 1) y
    rw [ih]
    change evalPRF H24_a_prf (mk_args2 (H24_c x y) (evalPRF H24_b_prf (mk_args3 x (H24_c x y) y))) = H24_a (H24_c x y) (H24_b x (H24_c x y) y)
    rw [H24_b_val, H24_a_val]

lemma H24_c_cf (x y : Nat) (h : x < y + 0) (hx : x > 0) : H24_c x y = y + 0 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H24_a (H24_c x y) (H24_b x (H24_c x y) y) = y + 0 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      have hy : y > 0 := by omega
      have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      rfl
    | inr hpos =>
      have h1 : x < y + 0 := by omega
      rw [ih h1 hpos]
      have h2 : y + 0 - x > 0 := by omega
      have h3 : ∃ k, y + 0 - x = k + 1 := by use (y + 0 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H24_a (k + 1) (H24_b x (k + 1) y) = y + 0 - (x + 1)
      change k = y + 0 - (x + 1)
      omega

lemma H24_comp (x : Nat) : evalPRF holdout_24 (fun _ => x) = evalPRF H24_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H24_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H24_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H24_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_24_diverges : ∀ x, evalPRF holdout_24 (fun _ => x) > 0 := by
  intro x
  rw [H24_comp x]
  cases x with
  | zero =>
    rw [H24_c_val]
    decide
  | succ x' =>
    rw [H24_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 0 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H24_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 25
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_25 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_25_diverges : ∀ x, evalPRF holdout_25 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 26
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_26 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H26_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H26_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H26_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H26_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H26_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H26_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H26_a (H26_c x' y) (H26_b x' (H26_c x' y) y)

lemma H26_a_val (x y : Nat) : evalPRF H26_a_prf (mk_args2 x y) = H26_a x y := by
  induction x <;> rfl

lemma H26_b_val (x acc y : Nat) : evalPRF H26_b_prf (mk_args3 x acc y) = H26_b x acc y := by
  induction x <;> rfl

lemma H26_c_val (x y : Nat) : evalPRF H26_c_prf (mk_args2 x y) = H26_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H26_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H26_b_prf]) (mk_args3 x (evalPRF H26_c_prf (mk_args2 x y)) y) = H26_c (x + 1) y
    rw [ih]
    change evalPRF H26_a_prf (mk_args2 (H26_c x y) (evalPRF H26_b_prf (mk_args3 x (H26_c x y) y))) = H26_a (H26_c x y) (H26_b x (H26_c x y) y)
    rw [H26_b_val, H26_a_val]

lemma H26_c_cf (x y : Nat) (h : x < y + 0) (hx : x > 0) : H26_c x y = y + 0 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H26_a (H26_c x y) (H26_b x (H26_c x y) y) = y + 0 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      have hy : y > 0 := by omega
      have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      rfl
    | inr hpos =>
      have h1 : x < y + 0 := by omega
      rw [ih h1 hpos]
      have h2 : y + 0 - x > 0 := by omega
      have h3 : ∃ k, y + 0 - x = k + 1 := by use (y + 0 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H26_a (k + 1) (H26_b x (k + 1) y) = y + 0 - (x + 1)
      change k = y + 0 - (x + 1)
      omega

lemma H26_comp (x : Nat) : evalPRF holdout_26 (fun _ => x) = evalPRF H26_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H26_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H26_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H26_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_26_diverges : ∀ x, evalPRF holdout_26 (fun _ => x) > 0 := by
  intro x
  rw [H26_comp x]
  cases x with
  | zero =>
    rw [H26_c_val]
    decide
  | succ x' =>
    rw [H26_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 0 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H26_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 27
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),S,P(1,1)))
def holdout_27 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_27_diverges : ∀ x, evalPRF holdout_27 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 28
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_28 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H28_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H28_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H28_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H28_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H28_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H28_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H28_a (H28_c x' y) (H28_b x' (H28_c x' y) y)

lemma H28_a_val (x y : Nat) : evalPRF H28_a_prf (mk_args2 x y) = H28_a x y := by
  induction x <;> rfl

lemma H28_b_val (x acc y : Nat) : evalPRF H28_b_prf (mk_args3 x acc y) = H28_b x acc y := by
  induction x <;> rfl

lemma H28_c_val (x y : Nat) : evalPRF H28_c_prf (mk_args2 x y) = H28_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H28_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H28_b_prf]) (mk_args3 x (evalPRF H28_c_prf (mk_args2 x y)) y) = H28_c (x + 1) y
    rw [ih]
    change evalPRF H28_a_prf (mk_args2 (H28_c x y) (evalPRF H28_b_prf (mk_args3 x (H28_c x y) y))) = H28_a (H28_c x y) (H28_b x (H28_c x y) y)
    rw [H28_b_val, H28_a_val]

lemma H28_c_cf (x y : Nat) (h : x < y + 0) (hx : x > 0) : H28_c x y = y + 0 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H28_a (H28_c x y) (H28_b x (H28_c x y) y) = y + 0 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      have hy : y > 0 := by omega
      have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      rfl
    | inr hpos =>
      have h1 : x < y + 0 := by omega
      rw [ih h1 hpos]
      have h2 : y + 0 - x > 0 := by omega
      have h3 : ∃ k, y + 0 - x = k + 1 := by use (y + 0 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H28_a (k + 1) (H28_b x (k + 1) y) = y + 0 - (x + 1)
      change k = y + 0 - (x + 1)
      omega

lemma H28_comp (x : Nat) : evalPRF holdout_28 (fun _ => x) = evalPRF H28_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H28_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H28_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H28_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_28_diverges : ∀ x, evalPRF holdout_28 (fun _ => x) > 0 := by
  intro x
  rw [H28_comp x]
  cases x with
  | zero =>
    rw [H28_c_val]
    decide
  | succ x' =>
    rw [H28_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 0 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H28_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 29
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,P(1,1)))
def holdout_29 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_29_diverges : ∀ x, evalPRF holdout_29 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 30
-- M(C(R(P(1,1),C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_30 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_30_diverges : ∀ x, evalPRF holdout_30 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 31
-- M(C(R(P(1,1),C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def holdout_31 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_31_diverges : ∀ x, evalPRF holdout_31 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 32
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,Z1))
def holdout_32 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_32_diverges : ∀ x, evalPRF holdout_32 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 33
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,P(1,1)))
def holdout_33 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_33_diverges : ∀ x, evalPRF holdout_33 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 34
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,S))
def holdout_34 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.succ]

theorem holdout_34_diverges : ∀ x, evalPRF holdout_34 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 35
-- M(C(R(P(1,1),C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),S))
def holdout_35 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_35_diverges : ∀ x, evalPRF holdout_35 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 36
-- M(C(R(P(1,1),R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_36 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_36_diverges : ∀ x, evalPRF holdout_36 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 37
-- M(C(R(P(1,1),R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_37 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_37_diverges : ∀ x, evalPRF holdout_37 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 38
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_38 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_38_diverges : ∀ x, evalPRF holdout_38 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 39
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_39 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_39_diverges : ∀ x, evalPRF holdout_39 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 40
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_40 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_40_diverges : ∀ x, evalPRF holdout_40 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 41
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_41 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_41_diverges : ∀ x, evalPRF holdout_41 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 42
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_42 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_42_diverges : ∀ x, evalPRF holdout_42 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 43
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_43 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_43_diverges : ∀ x, evalPRF holdout_43 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 44
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_44 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_44_diverges : ∀ x, evalPRF holdout_44 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 45
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_45 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_45_diverges : ∀ x, evalPRF holdout_45 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 46
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),S))
def holdout_46 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_46_diverges : ∀ x, evalPRF holdout_46 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 47
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def holdout_47 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_47_diverges : ∀ x, evalPRF holdout_47 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 48
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_48 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_48_diverges : ∀ x, evalPRF holdout_48 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 49
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_49 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_49_diverges : ∀ x, evalPRF holdout_49 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 50
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_50 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_50_diverges : ∀ x, evalPRF holdout_50 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 51
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_51 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_51_diverges : ∀ x, evalPRF holdout_51 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 52
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),P(1,1)))
def holdout_52 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

def H52_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H52_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H52_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H52_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H52_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H52_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H52_a (H52_c x' y) (H52_b x' (H52_c x' y) y)

lemma H52_a_val (x y : Nat) : evalPRF H52_a_prf (mk_args2 x y) = H52_a x y := by
  induction x <;> rfl

lemma H52_b_val (x acc y : Nat) : evalPRF H52_b_prf (mk_args3 x acc y) = H52_b x acc y := by
  induction x <;> rfl

lemma H52_c_val (x y : Nat) : evalPRF H52_c_prf (mk_args2 x y) = H52_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H52_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H52_b_prf]) (mk_args3 x (evalPRF H52_c_prf (mk_args2 x y)) y) = H52_c (x + 1) y
    rw [ih]
    change evalPRF H52_a_prf (mk_args2 (H52_c x y) (evalPRF H52_b_prf (mk_args3 x (H52_c x y) y))) = H52_a (H52_c x y) (H52_b x (H52_c x y) y)
    rw [H52_b_val, H52_a_val]

lemma H52_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H52_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H52_a (H52_c x y) (H52_b x (H52_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H52_a (k + 1) (H52_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H52_comp (x : Nat) : evalPRF holdout_52 (fun _ => x) = evalPRF H52_c_prf (mk_args2 x x) := by
  change evalPRF H52_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H52_c_prf (mk_args2 x x)
  apply congrArg (evalPRF H52_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_52_diverges : ∀ x, evalPRF holdout_52 (fun _ => x) > 0 := by
  intro x
  rw [H52_comp x]
  cases x with
  | zero =>
    rw [H52_c_val]
    decide
  | succ x' =>
    rw [H52_c_val]
    have h1 : (x' + 1) < (x' + 1) + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H52_c_cf ((x' + 1)) ((x' + 1)) h1 h2]
    omega

-- Translating holdout 53
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_53 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H53_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H53_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H53_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H53_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H53_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H53_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H53_a (H53_c x' y) (H53_b x' (H53_c x' y) y)

lemma H53_a_val (x y : Nat) : evalPRF H53_a_prf (mk_args2 x y) = H53_a x y := by
  induction x <;> rfl

lemma H53_b_val (x acc y : Nat) : evalPRF H53_b_prf (mk_args3 x acc y) = H53_b x acc y := by
  induction x <;> rfl

lemma H53_c_val (x y : Nat) : evalPRF H53_c_prf (mk_args2 x y) = H53_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H53_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H53_b_prf]) (mk_args3 x (evalPRF H53_c_prf (mk_args2 x y)) y) = H53_c (x + 1) y
    rw [ih]
    change evalPRF H53_a_prf (mk_args2 (H53_c x y) (evalPRF H53_b_prf (mk_args3 x (H53_c x y) y))) = H53_a (H53_c x y) (H53_b x (H53_c x y) y)
    rw [H53_b_val, H53_a_val]

lemma H53_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H53_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H53_a (H53_c x y) (H53_b x (H53_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H53_a (k + 1) (H53_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H53_comp (x : Nat) : evalPRF holdout_53 (fun _ => x) = evalPRF H53_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H53_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H53_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H53_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_53_diverges : ∀ x, evalPRF holdout_53 (fun _ => x) > 0 := by
  intro x
  rw [H53_comp x]
  cases x with
  | zero =>
    rw [H53_c_val]
    decide
  | succ x' =>
    rw [H53_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H53_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 54
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),S,S))
def holdout_54 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

def H54_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H54_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H54_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H54_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H54_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H54_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H54_a (H54_c x' y) (H54_b x' (H54_c x' y) y)

lemma H54_a_val (x y : Nat) : evalPRF H54_a_prf (mk_args2 x y) = H54_a x y := by
  induction x <;> rfl

lemma H54_b_val (x acc y : Nat) : evalPRF H54_b_prf (mk_args3 x acc y) = H54_b x acc y := by
  induction x <;> rfl

lemma H54_c_val (x y : Nat) : evalPRF H54_c_prf (mk_args2 x y) = H54_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H54_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H54_b_prf]) (mk_args3 x (evalPRF H54_c_prf (mk_args2 x y)) y) = H54_c (x + 1) y
    rw [ih]
    change evalPRF H54_a_prf (mk_args2 (H54_c x y) (evalPRF H54_b_prf (mk_args3 x (H54_c x y) y))) = H54_a (H54_c x y) (H54_b x (H54_c x y) y)
    rw [H54_b_val, H54_a_val]

lemma H54_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H54_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H54_a (H54_c x y) (H54_b x (H54_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H54_a (k + 1) (H54_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H54_comp (x : Nat) : evalPRF holdout_54 (fun _ => x) = evalPRF H54_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H54_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H54_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg (evalPRF H54_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_54_diverges : ∀ x, evalPRF holdout_54 (fun _ => x) > 0 := by
  intro x
  rw [H54_comp x]
  cases x with
  | zero =>
    rw [H54_c_val]
    decide
  | succ x' =>
    rw [H54_c_val]
    have h1 : (x' + 1)+1 < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1)+1 > 0 := by omega
    rw [H54_c_cf ((x' + 1)+1) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 55
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_55 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

def H55_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H55_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H55_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H55_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H55_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H55_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H55_a (H55_c x' y) (H55_b x' (H55_c x' y) y)

lemma H55_a_val (x y : Nat) : evalPRF H55_a_prf (mk_args2 x y) = H55_a x y := by
  induction x <;> rfl

lemma H55_b_val (x acc y : Nat) : evalPRF H55_b_prf (mk_args3 x acc y) = H55_b x acc y := by
  induction x <;> rfl

lemma H55_c_val (x y : Nat) : evalPRF H55_c_prf (mk_args2 x y) = H55_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H55_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H55_b_prf]) (mk_args3 x (evalPRF H55_c_prf (mk_args2 x y)) y) = H55_c (x + 1) y
    rw [ih]
    change evalPRF H55_a_prf (mk_args2 (H55_c x y) (evalPRF H55_b_prf (mk_args3 x (H55_c x y) y))) = H55_a (H55_c x y) (H55_b x (H55_c x y) y)
    rw [H55_b_val, H55_a_val]

lemma H55_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H55_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H55_a (H55_c x y) (H55_b x (H55_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H55_a (k + 1) (H55_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H55_comp (x : Nat) : evalPRF holdout_55 (fun _ => x) = evalPRF H55_c_prf (mk_args2 x x) := by
  change evalPRF H55_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H55_c_prf (mk_args2 x x)
  apply congrArg (evalPRF H55_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_55_diverges : ∀ x, evalPRF holdout_55 (fun _ => x) > 0 := by
  intro x
  rw [H55_comp x]
  cases x with
  | zero =>
    rw [H55_c_val]
    decide
  | succ x' =>
    rw [H55_c_val]
    have h1 : (x' + 1) < (x' + 1) + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H55_c_cf ((x' + 1)) ((x' + 1)) h1 h2]
    omega

-- Translating holdout 56
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_56 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H56_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H56_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H56_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H56_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H56_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H56_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H56_a (H56_c x' y) (H56_b x' (H56_c x' y) y)

lemma H56_a_val (x y : Nat) : evalPRF H56_a_prf (mk_args2 x y) = H56_a x y := by
  induction x <;> rfl

lemma H56_b_val (x acc y : Nat) : evalPRF H56_b_prf (mk_args3 x acc y) = H56_b x acc y := by
  induction x <;> rfl

lemma H56_c_val (x y : Nat) : evalPRF H56_c_prf (mk_args2 x y) = H56_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H56_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H56_b_prf]) (mk_args3 x (evalPRF H56_c_prf (mk_args2 x y)) y) = H56_c (x + 1) y
    rw [ih]
    change evalPRF H56_a_prf (mk_args2 (H56_c x y) (evalPRF H56_b_prf (mk_args3 x (H56_c x y) y))) = H56_a (H56_c x y) (H56_b x (H56_c x y) y)
    rw [H56_b_val, H56_a_val]

lemma H56_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H56_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H56_a (H56_c x y) (H56_b x (H56_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H56_a (k + 1) (H56_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H56_comp (x : Nat) : evalPRF holdout_56 (fun _ => x) = evalPRF H56_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H56_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H56_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H56_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_56_diverges : ∀ x, evalPRF holdout_56 (fun _ => x) > 0 := by
  intro x
  rw [H56_comp x]
  cases x with
  | zero =>
    rw [H56_c_val]
    decide
  | succ x' =>
    rw [H56_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H56_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 57
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_57 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

def H57_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H57_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H57_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H57_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H57_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H57_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H57_a (H57_c x' y) (H57_b x' (H57_c x' y) y)

lemma H57_a_val (x y : Nat) : evalPRF H57_a_prf (mk_args2 x y) = H57_a x y := by
  induction x <;> rfl

lemma H57_b_val (x acc y : Nat) : evalPRF H57_b_prf (mk_args3 x acc y) = H57_b x acc y := by
  induction x <;> rfl

lemma H57_c_val (x y : Nat) : evalPRF H57_c_prf (mk_args2 x y) = H57_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H57_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H57_b_prf]) (mk_args3 x (evalPRF H57_c_prf (mk_args2 x y)) y) = H57_c (x + 1) y
    rw [ih]
    change evalPRF H57_a_prf (mk_args2 (H57_c x y) (evalPRF H57_b_prf (mk_args3 x (H57_c x y) y))) = H57_a (H57_c x y) (H57_b x (H57_c x y) y)
    rw [H57_b_val, H57_a_val]

lemma H57_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H57_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H57_a (H57_c x y) (H57_b x (H57_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H57_a (k + 1) (H57_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H57_comp (x : Nat) : evalPRF holdout_57 (fun _ => x) = evalPRF H57_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H57_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H57_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg (evalPRF H57_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_57_diverges : ∀ x, evalPRF holdout_57 (fun _ => x) > 0 := by
  intro x
  rw [H57_comp x]
  cases x with
  | zero =>
    rw [H57_c_val]
    decide
  | succ x' =>
    rw [H57_c_val]
    have h1 : (x' + 1)+1 < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1)+1 > 0 := by omega
    rw [H57_c_cf ((x' + 1)+1) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 58
-- M(C(R(S,C(R(P(1,1),P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_58 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_58_diverges : ∀ x, evalPRF holdout_58 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 59
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),P(1,1)))
def holdout_59 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

def H59_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H59_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H59_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H59_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H59_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H59_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H59_a (H59_c x' y) (H59_b x' (H59_c x' y) y)

lemma H59_a_val (x y : Nat) : evalPRF H59_a_prf (mk_args2 x y) = H59_a x y := by
  induction x <;> rfl

lemma H59_b_val (x acc y : Nat) : evalPRF H59_b_prf (mk_args3 x acc y) = H59_b x acc y := by
  induction x <;> rfl

lemma H59_c_val (x y : Nat) : evalPRF H59_c_prf (mk_args2 x y) = H59_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H59_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H59_b_prf]) (mk_args3 x (evalPRF H59_c_prf (mk_args2 x y)) y) = H59_c (x + 1) y
    rw [ih]
    change evalPRF H59_a_prf (mk_args2 (H59_c x y) (evalPRF H59_b_prf (mk_args3 x (H59_c x y) y))) = H59_a (H59_c x y) (H59_b x (H59_c x y) y)
    rw [H59_b_val, H59_a_val]

lemma H59_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H59_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H59_a (H59_c x y) (H59_b x (H59_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H59_a (k + 1) (H59_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H59_comp (x : Nat) : evalPRF holdout_59 (fun _ => x) = evalPRF H59_c_prf (mk_args2 x x) := by
  change evalPRF H59_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H59_c_prf (mk_args2 x x)
  apply congrArg (evalPRF H59_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_59_diverges : ∀ x, evalPRF holdout_59 (fun _ => x) > 0 := by
  intro x
  rw [H59_comp x]
  cases x with
  | zero =>
    rw [H59_c_val]
    decide
  | succ x' =>
    rw [H59_c_val]
    have h1 : (x' + 1) < (x' + 1) + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H59_c_cf ((x' + 1)) ((x' + 1)) h1 h2]
    omega

-- Translating holdout 60
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_60 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H60_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H60_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H60_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H60_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H60_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H60_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H60_a (H60_c x' y) (H60_b x' (H60_c x' y) y)

lemma H60_a_val (x y : Nat) : evalPRF H60_a_prf (mk_args2 x y) = H60_a x y := by
  induction x <;> rfl

lemma H60_b_val (x acc y : Nat) : evalPRF H60_b_prf (mk_args3 x acc y) = H60_b x acc y := by
  induction x <;> rfl

lemma H60_c_val (x y : Nat) : evalPRF H60_c_prf (mk_args2 x y) = H60_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H60_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H60_b_prf]) (mk_args3 x (evalPRF H60_c_prf (mk_args2 x y)) y) = H60_c (x + 1) y
    rw [ih]
    change evalPRF H60_a_prf (mk_args2 (H60_c x y) (evalPRF H60_b_prf (mk_args3 x (H60_c x y) y))) = H60_a (H60_c x y) (H60_b x (H60_c x y) y)
    rw [H60_b_val, H60_a_val]

lemma H60_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H60_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H60_a (H60_c x y) (H60_b x (H60_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H60_a (k + 1) (H60_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H60_comp (x : Nat) : evalPRF holdout_60 (fun _ => x) = evalPRF H60_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H60_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H60_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H60_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_60_diverges : ∀ x, evalPRF holdout_60 (fun _ => x) > 0 := by
  intro x
  rw [H60_comp x]
  cases x with
  | zero =>
    rw [H60_c_val]
    decide
  | succ x' =>
    rw [H60_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H60_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 61
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),S,S))
def holdout_61 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

def H61_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H61_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H61_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H61_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H61_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => x'

def H61_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H61_a (H61_c x' y) (H61_b x' (H61_c x' y) y)

lemma H61_a_val (x y : Nat) : evalPRF H61_a_prf (mk_args2 x y) = H61_a x y := by
  induction x <;> rfl

lemma H61_b_val (x acc y : Nat) : evalPRF H61_b_prf (mk_args3 x acc y) = H61_b x acc y := by
  induction x <;> rfl

lemma H61_c_val (x y : Nat) : evalPRF H61_c_prf (mk_args2 x y) = H61_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H61_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H61_b_prf]) (mk_args3 x (evalPRF H61_c_prf (mk_args2 x y)) y) = H61_c (x + 1) y
    rw [ih]
    change evalPRF H61_a_prf (mk_args2 (H61_c x y) (evalPRF H61_b_prf (mk_args3 x (H61_c x y) y))) = H61_a (H61_c x y) (H61_b x (H61_c x y) y)
    rw [H61_b_val, H61_a_val]

lemma H61_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H61_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H61_a (H61_c x y) (H61_b x (H61_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H61_a (k + 1) (H61_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H61_comp (x : Nat) : evalPRF holdout_61 (fun _ => x) = evalPRF H61_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H61_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H61_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg (evalPRF H61_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_61_diverges : ∀ x, evalPRF holdout_61 (fun _ => x) > 0 := by
  intro x
  rw [H61_comp x]
  cases x with
  | zero =>
    rw [H61_c_val]
    decide
  | succ x' =>
    rw [H61_c_val]
    have h1 : (x' + 1)+1 < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1)+1 > 0 := by omega
    rw [H61_c_cf ((x' + 1)+1) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 62
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_62 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

def H62_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H62_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H62_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H62_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H62_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H62_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H62_a (H62_c x' y) (H62_b x' (H62_c x' y) y)

lemma H62_a_val (x y : Nat) : evalPRF H62_a_prf (mk_args2 x y) = H62_a x y := by
  induction x <;> rfl

lemma H62_b_val (x acc y : Nat) : evalPRF H62_b_prf (mk_args3 x acc y) = H62_b x acc y := by
  induction x <;> rfl

lemma H62_c_val (x y : Nat) : evalPRF H62_c_prf (mk_args2 x y) = H62_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H62_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H62_b_prf]) (mk_args3 x (evalPRF H62_c_prf (mk_args2 x y)) y) = H62_c (x + 1) y
    rw [ih]
    change evalPRF H62_a_prf (mk_args2 (H62_c x y) (evalPRF H62_b_prf (mk_args3 x (H62_c x y) y))) = H62_a (H62_c x y) (H62_b x (H62_c x y) y)
    rw [H62_b_val, H62_a_val]

lemma H62_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H62_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H62_a (H62_c x y) (H62_b x (H62_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H62_a (k + 1) (H62_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H62_comp (x : Nat) : evalPRF holdout_62 (fun _ => x) = evalPRF H62_c_prf (mk_args2 x x) := by
  change evalPRF H62_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H62_c_prf (mk_args2 x x)
  apply congrArg (evalPRF H62_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_62_diverges : ∀ x, evalPRF holdout_62 (fun _ => x) > 0 := by
  intro x
  rw [H62_comp x]
  cases x with
  | zero =>
    rw [H62_c_val]
    decide
  | succ x' =>
    rw [H62_c_val]
    have h1 : (x' + 1) < (x' + 1) + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H62_c_cf ((x' + 1)) ((x' + 1)) h1 h2]
    omega

-- Translating holdout 63
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_63 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H63_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H63_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H63_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H63_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H63_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H63_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H63_a (H63_c x' y) (H63_b x' (H63_c x' y) y)

lemma H63_a_val (x y : Nat) : evalPRF H63_a_prf (mk_args2 x y) = H63_a x y := by
  induction x <;> rfl

lemma H63_b_val (x acc y : Nat) : evalPRF H63_b_prf (mk_args3 x acc y) = H63_b x acc y := by
  induction x <;> rfl

lemma H63_c_val (x y : Nat) : evalPRF H63_c_prf (mk_args2 x y) = H63_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H63_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H63_b_prf]) (mk_args3 x (evalPRF H63_c_prf (mk_args2 x y)) y) = H63_c (x + 1) y
    rw [ih]
    change evalPRF H63_a_prf (mk_args2 (H63_c x y) (evalPRF H63_b_prf (mk_args3 x (H63_c x y) y))) = H63_a (H63_c x y) (H63_b x (H63_c x y) y)
    rw [H63_b_val, H63_a_val]

lemma H63_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H63_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H63_a (H63_c x y) (H63_b x (H63_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H63_a (k + 1) (H63_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H63_comp (x : Nat) : evalPRF holdout_63 (fun _ => x) = evalPRF H63_c_prf (mk_args2 x (x+1)) := by
  change evalPRF H63_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = evalPRF H63_c_prf (mk_args2 x (x+1))
  apply congrArg (evalPRF H63_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_63_diverges : ∀ x, evalPRF holdout_63 (fun _ => x) > 0 := by
  intro x
  rw [H63_comp x]
  cases x with
  | zero =>
    rw [H63_c_val]
    decide
  | succ x' =>
    rw [H63_c_val]
    have h1 : (x' + 1) < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1) > 0 := by omega
    rw [H63_c_cf ((x' + 1)) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 64
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_64 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

def H64_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H64_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H64_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H64_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H64_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H64_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H64_a (H64_c x' y) (H64_b x' (H64_c x' y) y)

lemma H64_a_val (x y : Nat) : evalPRF H64_a_prf (mk_args2 x y) = H64_a x y := by
  induction x <;> rfl

lemma H64_b_val (x acc y : Nat) : evalPRF H64_b_prf (mk_args3 x acc y) = H64_b x acc y := by
  induction x <;> rfl

lemma H64_c_val (x y : Nat) : evalPRF H64_c_prf (mk_args2 x y) = H64_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H64_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H64_b_prf]) (mk_args3 x (evalPRF H64_c_prf (mk_args2 x y)) y) = H64_c (x + 1) y
    rw [ih]
    change evalPRF H64_a_prf (mk_args2 (H64_c x y) (evalPRF H64_b_prf (mk_args3 x (H64_c x y) y))) = H64_a (H64_c x y) (H64_b x (H64_c x y) y)
    rw [H64_b_val, H64_a_val]

lemma H64_c_cf (x y : Nat) (h : x < y + 1) (hx : x > 0) : H64_c x y = y + 1 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H64_a (H64_c x y) (H64_b x (H64_c x y) y) = y + 1 - (x + 1)
    have hcases : x = 0 ∨ x > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x < y + 1 := by omega
      rw [ih h1 hpos]
      have h2 : y + 1 - x > 0 := by omega
      have h3 : ∃ k, y + 1 - x = k + 1 := by use (y + 1 - x - 1); omega
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change H64_a (k + 1) (H64_b x (k + 1) y) = y + 1 - (x + 1)
      change k = y + 1 - (x + 1)
      omega

lemma H64_comp (x : Nat) : evalPRF holdout_64 (fun _ => x) = evalPRF H64_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H64_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H64_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg (evalPRF H64_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_64_diverges : ∀ x, evalPRF holdout_64 (fun _ => x) > 0 := by
  intro x
  rw [H64_comp x]
  cases x with
  | zero =>
    rw [H64_c_val]
    decide
  | succ x' =>
    rw [H64_c_val]
    have h1 : (x' + 1)+1 < (x' + 1)+1 + 1 := by omega
    have h2 : (x' + 1)+1 > 0 := by omega
    rw [H64_c_cf ((x' + 1)+1) ((x' + 1)+1) h1 h2]
    omega

-- Translating holdout 65
-- M(C(R(S,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_65 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_65_diverges : ∀ x, evalPRF holdout_65 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 66
-- M(C(R(S,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def holdout_66 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_66_diverges : ∀ x, evalPRF holdout_66 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 67
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),P(1,1),Z1))
def holdout_67 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1]

theorem holdout_67_diverges : ∀ x, evalPRF holdout_67 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 68
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,Z1))
def holdout_68 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_68_diverges : ∀ x, evalPRF holdout_68 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 69
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,P(1,1)))
def holdout_69 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_69_diverges : ∀ x, evalPRF holdout_69 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 70
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),P(1,1)))
def holdout_70 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_70_diverges : ∀ x, evalPRF holdout_70 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 71
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),S))
def holdout_71 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_71_diverges : ∀ x, evalPRF holdout_71 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 72
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),S,S))
def holdout_72 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, PRF.succ]

theorem holdout_72_diverges : ∀ x, evalPRF holdout_72 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 73
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_73 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_73_diverges : ∀ x, evalPRF holdout_73 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 74
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_74 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_74_diverges : ∀ x, evalPRF holdout_74 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 75
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,P(1,1)))
def holdout_75 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_75_diverges : ∀ x, evalPRF holdout_75 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 76
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_76 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_76_diverges : ∀ x, evalPRF holdout_76 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 77
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_77 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_77_diverges : ∀ x, evalPRF holdout_77 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 78
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_78 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_78_diverges : ∀ x, evalPRF holdout_78 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 79
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,P(1,1)))
def holdout_79 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_79_diverges : ∀ x, evalPRF holdout_79 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 80
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_80 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_80_diverges : ∀ x, evalPRF holdout_80 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 81
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),P(1,1)))
def holdout_81 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_81_diverges : ∀ x, evalPRF holdout_81 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 82
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_82 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_82_diverges : ∀ x, evalPRF holdout_82 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 83
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,P(1,1)))
def holdout_83 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_83_diverges : ∀ x, evalPRF holdout_83 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 84
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_84 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_84_diverges : ∀ x, evalPRF holdout_84 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 85
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_85 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_85_diverges : ∀ x, evalPRF holdout_85 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 86
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_86 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_86_diverges : ∀ x, evalPRF holdout_86 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 87
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_87 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_87_diverges : ∀ x, evalPRF holdout_87 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 88
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_88 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_88_diverges : ∀ x, evalPRF holdout_88 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 89
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_89 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_89_diverges : ∀ x, evalPRF holdout_89 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 90
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_90 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_90_diverges : ∀ x, evalPRF holdout_90 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 91
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_91 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_91_diverges : ∀ x, evalPRF holdout_91 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 92
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),P(1,1)))
def holdout_92 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_92_diverges : ∀ x, evalPRF holdout_92 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 93
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),S))
def holdout_93 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_93_diverges : ∀ x, evalPRF holdout_93 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 94
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def holdout_94 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_94_diverges : ∀ x, evalPRF holdout_94 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 95
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_95 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_95_diverges : ∀ x, evalPRF holdout_95 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 96
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_96 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_96_diverges : ∀ x, evalPRF holdout_96 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 97
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_97 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_97_diverges : ∀ x, evalPRF holdout_97 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 98
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),P(1,1)))
def holdout_98 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_98_diverges : ∀ x, evalPRF holdout_98 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 99
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_99 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_99_diverges : ∀ x, evalPRF holdout_99 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 100
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_100 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_100_diverges : ∀ x, evalPRF holdout_100 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 101
-- M(R(C(S,Z0),R(P(1,1),C(R(Z0,R(S,P(3,1))),P(3,2)))))
def holdout_101 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)]))

theorem holdout_101_diverges : ∀ x, evalPRF holdout_101 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 102
-- M(R(C(S,Z0),R(P(1,1),R(R(Z1,R(P(2,2),P(4,1))),P(4,2)))))
def holdout_102 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_102_diverges : ∀ x, evalPRF holdout_102 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 103
-- M(R(C(S,Z0),R(P(1,1),R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2)))))
def holdout_103 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_103_diverges : ∀ x, evalPRF holdout_103 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 104
-- M(R(C(S,Z0),R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2)))))
def holdout_104 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_104_diverges : ∀ x, evalPRF holdout_104 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 105
-- M(R(C(S,Z0),R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2)))))
def holdout_105 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_105_diverges : ∀ x, evalPRF holdout_105 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 106
-- M(R(C(S,Z0),R(S,R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2)))))
def holdout_106 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_106_diverges : ∀ x, evalPRF holdout_106 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 107
-- M(R(C(S,Z0),R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2)))))
def holdout_107 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_107_diverges : ∀ x, evalPRF holdout_107 (fun _ => x) > 0 := by
  sorry

end Holdouts14
