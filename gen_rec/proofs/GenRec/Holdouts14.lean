import GenRec.Semantics
set_option maxHeartbeats 4000000


open GenRec

namespace Holdouts14

def mk_args2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
def mk_args3 (a b c : Nat) : Fin 3 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else c
def mk_args4 (a b c d : Nat) : Fin 4 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d
def mk_args5 (a b c d e : Nat) : Fin 5 → Nat := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else if i.val = 3 then d else e



-- Translating holdout 0
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_0 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

def H0_sub_1_prf : PRF 1 := PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))
def H0_sub_1 (x : Nat) : Nat := x - 1
lemma H0_sub_1_val (x : Nat) : evalPRF H0_sub_1_prf (fun _ => x) = H0_sub_1 x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change evalPRF ((PRF.proj 2 ⟨0, by decide⟩)) (mk_args2 x' (evalPRF H0_sub_1_prf (fun _ => x'))) = H0_sub_1 (x' + 1)
    change x' = x' + 1 - 1
    omega

def H0_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H0_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H0_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H0_a (x y : Nat) : Nat := match x with
  | 0 => y
  | x' + 1 => x'
def H0_b (x _acc _y : Nat) : Nat := x

lemma H0_a_val (x y : Nat) : evalPRF H0_a_prf (mk_args2 x y) = H0_a x y := by
  cases x <;> rfl

lemma H0_b_val (x acc y : Nat) : evalPRF H0_b_prf (mk_args3 x acc y) = H0_b x acc y := by
  rfl

def H0_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H0_a (H0_c x' y) (H0_b x' (H0_c x' y) y)

lemma H0_c_val (x y : Nat) : evalPRF H0_c_prf (mk_args2 x y) = H0_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H0_a_prf (mk_args2 (evalPRF H0_c_prf (mk_args2 x' y)) (evalPRF H0_b_prf (mk_args3 x' (evalPRF H0_c_prf (mk_args2 x' y)) y))) = H0_a (H0_c x' y) (H0_b x' (H0_c x' y) y)
    rw [ih, H0_a_val, H0_b_val]


lemma H0_c_cf (x y : Nat) (h : x ≤ y + 0) : H0_c x y = y + 0 - x := by
  induction x with
  | zero => exact (Nat.sub_zero (y + 0)).symm
  | succ x' ih =>
    change H0_a (H0_c x' y) (H0_b x' (H0_c x' y) y) = y + 0 - (x' + 1)
    have h1 : x' ≤ y + 0 := by omega
    rw [ih h1]
    change H0_a (y + 0 - x') x' = y + 0 - (x' + 1)
    have h2 : y + 0 - x' > 0 := by omega
    have h3 : ∃ k, y + 0 - x' = k + 1 := by use (y + 0 - x' - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y + 0 - (x' + 1)
    omega

lemma H0_comp (x : Nat) : evalPRF holdout_0 (fun _ => x) = evalPRF H0_c_prf (mk_args2 ((evalPRF H0_sub_1_prf (fun _ => x))) (x + 1)) := by
  change evalPRF H0_c_prf (fun j => evalPRFList prf_list![H0_sub_1_prf, PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_0_diverges : ∀ x, evalPRF holdout_0 (fun _ => x) > 0 := by
  intro x
  rw [H0_comp x]
  rw [H0_sub_1_val]
  unfold H0_sub_1
  rw [H0_c_val]
  rw [H0_c_cf _ _ (by omega)]
  omega

-- Translating holdout 1
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_1 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

def H1_sub_1_prf : PRF 1 := PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))
def H1_sub_1 (x : Nat) : Nat := x - 1
lemma H1_sub_1_val (x : Nat) : evalPRF H1_sub_1_prf (fun _ => x) = H1_sub_1 x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change evalPRF ((PRF.proj 2 ⟨0, by decide⟩)) (mk_args2 x' (evalPRF H1_sub_1_prf (fun _ => x'))) = H1_sub_1 (x' + 1)
    change x' = x' + 1 - 1
    omega

def H1_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H1_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H1_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H1_a (x y : Nat) : Nat := match x with
  | 0 => y + 1
  | x' + 1 => x'
def H1_b (x _acc _y : Nat) : Nat := x

lemma H1_a_val (x y : Nat) : evalPRF H1_a_prf (mk_args2 x y) = H1_a x y := by
  cases x <;> rfl

lemma H1_b_val (x acc y : Nat) : evalPRF H1_b_prf (mk_args3 x acc y) = H1_b x acc y := by
  rfl

def H1_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H1_a (H1_c x' y) (H1_b x' (H1_c x' y) y)

lemma H1_c_val (x y : Nat) : evalPRF H1_c_prf (mk_args2 x y) = H1_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H1_a_prf (mk_args2 (evalPRF H1_c_prf (mk_args2 x' y)) (evalPRF H1_b_prf (mk_args3 x' (evalPRF H1_c_prf (mk_args2 x' y)) y))) = H1_a (H1_c x' y) (H1_b x' (H1_c x' y) y)
    rw [ih, H1_a_val, H1_b_val]


lemma H1_c_cf (x y : Nat) (h : x ≤ y + 0) : H1_c x y = y + 0 - x := by
  induction x with
  | zero => exact (Nat.sub_zero (y + 0)).symm
  | succ x' ih =>
    change H1_a (H1_c x' y) (H1_b x' (H1_c x' y) y) = y + 0 - (x' + 1)
    have h1 : x' ≤ y + 0 := by omega
    rw [ih h1]
    change H1_a (y + 0 - x') x' = y + 0 - (x' + 1)
    have h2 : y + 0 - x' > 0 := by omega
    have h3 : ∃ k, y + 0 - x' = k + 1 := by use (y + 0 - x' - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y + 0 - (x' + 1)
    omega

lemma H1_comp (x : Nat) : evalPRF holdout_1 (fun _ => x) = evalPRF H1_c_prf (mk_args2 ((evalPRF H1_sub_1_prf (fun _ => x))) (x + 1)) := by
  change evalPRF H1_c_prf (fun j => evalPRFList prf_list![H1_sub_1_prf, PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_1_diverges : ∀ x, evalPRF holdout_1 (fun _ => x) > 0 := by
  intro x
  rw [H1_comp x]
  rw [H1_sub_1_val]
  unfold H1_sub_1
  rw [H1_c_val]
  rw [H1_c_cf _ _ (by omega)]
  omega

-- Translating holdout 2
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),P(1,1)))
def holdout_2 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), (PRF.proj 1 ⟨0, by decide⟩)]

def H2_sub_1_prf : PRF 1 := PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))
def H2_sub_1 (x : Nat) : Nat := x - 1
lemma H2_sub_1_val (x : Nat) : evalPRF H2_sub_1_prf (fun _ => x) = H2_sub_1 x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change evalPRF ((PRF.proj 2 ⟨0, by decide⟩)) (mk_args2 x' (evalPRF H2_sub_1_prf (fun _ => x'))) = H2_sub_1 (x' + 1)
    change x' = x' + 1 - 1
    omega

def H2_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H2_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H2_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H2_a (x y : Nat) : Nat := match x with
  | 0 => y
  | x' + 1 => x'
def H2_b (x _acc _y : Nat) : Nat := x

lemma H2_a_val (x y : Nat) : evalPRF H2_a_prf (mk_args2 x y) = H2_a x y := by
  cases x <;> rfl

lemma H2_b_val (x acc y : Nat) : evalPRF H2_b_prf (mk_args3 x acc y) = H2_b x acc y := by
  rfl

def H2_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H2_a (H2_c x' y) (H2_b x' (H2_c x' y) y)

lemma H2_c_val (x y : Nat) : evalPRF H2_c_prf (mk_args2 x y) = H2_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H2_a_prf (mk_args2 (evalPRF H2_c_prf (mk_args2 x' y)) (evalPRF H2_b_prf (mk_args3 x' (evalPRF H2_c_prf (mk_args2 x' y)) y))) = H2_a (H2_c x' y) (H2_b x' (H2_c x' y) y)
    rw [ih, H2_a_val, H2_b_val]


lemma H2_c_cf (x y : Nat) (h : x ≤ y + 1) : H2_c x y = y + 1 - x := by
  induction x with
  | zero => exact (Nat.sub_zero (y + 1)).symm
  | succ x' ih =>
    change H2_a (H2_c x' y) (H2_b x' (H2_c x' y) y) = y + 1 - (x' + 1)
    have h1 : x' ≤ y + 1 := by omega
    rw [ih h1]
    change H2_a (y + 1 - x') x' = y + 1 - (x' + 1)
    have h2 : y + 1 - x' > 0 := by omega
    have h3 : ∃ k, y + 1 - x' = k + 1 := by use (y + 1 - x' - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y + 1 - (x' + 1)
    omega

lemma H2_comp (x : Nat) : evalPRF holdout_2 (fun _ => x) = evalPRF H2_c_prf (mk_args2 ((evalPRF H2_sub_1_prf (fun _ => x))) (x)) := by
  change evalPRF H2_c_prf (fun j => evalPRFList prf_list![H2_sub_1_prf, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_2_diverges : ∀ x, evalPRF holdout_2 (fun _ => x) > 0 := by
  intro x
  rw [H2_comp x]
  rw [H2_sub_1_val]
  unfold H2_sub_1
  rw [H2_c_val]
  rw [H2_c_cf _ _ (by omega)]
  omega

-- Translating holdout 3
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_3 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

def H3_sub_1_prf : PRF 1 := PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))
def H3_sub_1 (x : Nat) : Nat := x - 1
lemma H3_sub_1_val (x : Nat) : evalPRF H3_sub_1_prf (fun _ => x) = H3_sub_1 x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change evalPRF ((PRF.proj 2 ⟨0, by decide⟩)) (mk_args2 x' (evalPRF H3_sub_1_prf (fun _ => x'))) = H3_sub_1 (x' + 1)
    change x' = x' + 1 - 1
    omega

def H3_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H3_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H3_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H3_a (x y : Nat) : Nat := match x with
  | 0 => y
  | x' + 1 => x'
def H3_b (x _acc _y : Nat) : Nat := x

lemma H3_a_val (x y : Nat) : evalPRF H3_a_prf (mk_args2 x y) = H3_a x y := by
  cases x <;> rfl

lemma H3_b_val (x acc y : Nat) : evalPRF H3_b_prf (mk_args3 x acc y) = H3_b x acc y := by
  rfl

def H3_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H3_a (H3_c x' y) (H3_b x' (H3_c x' y) y)

lemma H3_c_val (x y : Nat) : evalPRF H3_c_prf (mk_args2 x y) = H3_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H3_a_prf (mk_args2 (evalPRF H3_c_prf (mk_args2 x' y)) (evalPRF H3_b_prf (mk_args3 x' (evalPRF H3_c_prf (mk_args2 x' y)) y))) = H3_a (H3_c x' y) (H3_b x' (H3_c x' y) y)
    rw [ih, H3_a_val, H3_b_val]


lemma H3_c_cf (x y : Nat) (h : x ≤ y + 1) : H3_c x y = y + 1 - x := by
  induction x with
  | zero => exact (Nat.sub_zero (y + 1)).symm
  | succ x' ih =>
    change H3_a (H3_c x' y) (H3_b x' (H3_c x' y) y) = y + 1 - (x' + 1)
    have h1 : x' ≤ y + 1 := by omega
    rw [ih h1]
    change H3_a (y + 1 - x') x' = y + 1 - (x' + 1)
    have h2 : y + 1 - x' > 0 := by omega
    have h3 : ∃ k, y + 1 - x' = k + 1 := by use (y + 1 - x' - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y + 1 - (x' + 1)
    omega

lemma H3_comp (x : Nat) : evalPRF holdout_3 (fun _ => x) = evalPRF H3_c_prf (mk_args2 ((evalPRF H3_sub_1_prf (fun _ => x))) (x + 1)) := by
  change evalPRF H3_c_prf (fun j => evalPRFList prf_list![H3_sub_1_prf, PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_3_diverges : ∀ x, evalPRF holdout_3 (fun _ => x) > 0 := by
  intro x
  rw [H3_comp x]
  rw [H3_sub_1_val]
  unfold H3_sub_1
  rw [H3_c_val]
  rw [H3_c_cf _ _ (by omega)]
  omega

-- Translating holdout 4
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),P(1,1)))
def holdout_4 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), (PRF.proj 1 ⟨0, by decide⟩)]

def H4_sub_1_prf : PRF 1 := PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))
def H4_sub_1 (x : Nat) : Nat := x - 1
lemma H4_sub_1_val (x : Nat) : evalPRF H4_sub_1_prf (fun _ => x) = H4_sub_1 x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change evalPRF ((PRF.proj 2 ⟨0, by decide⟩)) (mk_args2 x' (evalPRF H4_sub_1_prf (fun _ => x'))) = H4_sub_1 (x' + 1)
    change x' = x' + 1 - 1
    omega

def H4_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H4_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H4_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H4_a (x y : Nat) : Nat := match x with
  | 0 => y + 1
  | x' + 1 => x'
def H4_b (x _acc _y : Nat) : Nat := x

lemma H4_a_val (x y : Nat) : evalPRF H4_a_prf (mk_args2 x y) = H4_a x y := by
  cases x <;> rfl

lemma H4_b_val (x acc y : Nat) : evalPRF H4_b_prf (mk_args3 x acc y) = H4_b x acc y := by
  rfl

def H4_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H4_a (H4_c x' y) (H4_b x' (H4_c x' y) y)

lemma H4_c_val (x y : Nat) : evalPRF H4_c_prf (mk_args2 x y) = H4_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H4_a_prf (mk_args2 (evalPRF H4_c_prf (mk_args2 x' y)) (evalPRF H4_b_prf (mk_args3 x' (evalPRF H4_c_prf (mk_args2 x' y)) y))) = H4_a (H4_c x' y) (H4_b x' (H4_c x' y) y)
    rw [ih, H4_a_val, H4_b_val]


lemma H4_c_cf (x y : Nat) (h : x ≤ y + 1) : H4_c x y = y + 1 - x := by
  induction x with
  | zero => exact (Nat.sub_zero (y + 1)).symm
  | succ x' ih =>
    change H4_a (H4_c x' y) (H4_b x' (H4_c x' y) y) = y + 1 - (x' + 1)
    have h1 : x' ≤ y + 1 := by omega
    rw [ih h1]
    change H4_a (y + 1 - x') x' = y + 1 - (x' + 1)
    have h2 : y + 1 - x' > 0 := by omega
    have h3 : ∃ k, y + 1 - x' = k + 1 := by use (y + 1 - x' - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y + 1 - (x' + 1)
    omega

lemma H4_comp (x : Nat) : evalPRF holdout_4 (fun _ => x) = evalPRF H4_c_prf (mk_args2 ((evalPRF H4_sub_1_prf (fun _ => x))) (x)) := by
  change evalPRF H4_c_prf (fun j => evalPRFList prf_list![H4_sub_1_prf, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_4_diverges : ∀ x, evalPRF holdout_4 (fun _ => x) > 0 := by
  intro x
  rw [H4_comp x]
  rw [H4_sub_1_val]
  unfold H4_sub_1
  rw [H4_c_val]
  rw [H4_c_cf _ _ (by omega)]
  omega

-- Translating holdout 5
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_5 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

def H5_sub_1_prf : PRF 1 := PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))
def H5_sub_1 (x : Nat) : Nat := x - 1
lemma H5_sub_1_val (x : Nat) : evalPRF H5_sub_1_prf (fun _ => x) = H5_sub_1 x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change evalPRF ((PRF.proj 2 ⟨0, by decide⟩)) (mk_args2 x' (evalPRF H5_sub_1_prf (fun _ => x'))) = H5_sub_1 (x' + 1)
    change x' = x' + 1 - 1
    omega

def H5_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H5_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H5_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H5_a (x y : Nat) : Nat := match x with
  | 0 => y + 1
  | x' + 1 => x'
def H5_b (x _acc _y : Nat) : Nat := x

lemma H5_a_val (x y : Nat) : evalPRF H5_a_prf (mk_args2 x y) = H5_a x y := by
  cases x <;> rfl

lemma H5_b_val (x acc y : Nat) : evalPRF H5_b_prf (mk_args3 x acc y) = H5_b x acc y := by
  rfl

def H5_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H5_a (H5_c x' y) (H5_b x' (H5_c x' y) y)

lemma H5_c_val (x y : Nat) : evalPRF H5_c_prf (mk_args2 x y) = H5_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H5_a_prf (mk_args2 (evalPRF H5_c_prf (mk_args2 x' y)) (evalPRF H5_b_prf (mk_args3 x' (evalPRF H5_c_prf (mk_args2 x' y)) y))) = H5_a (H5_c x' y) (H5_b x' (H5_c x' y) y)
    rw [ih, H5_a_val, H5_b_val]


lemma H5_c_cf (x y : Nat) (h : x ≤ y + 1) : H5_c x y = y + 1 - x := by
  induction x with
  | zero => exact (Nat.sub_zero (y + 1)).symm
  | succ x' ih =>
    change H5_a (H5_c x' y) (H5_b x' (H5_c x' y) y) = y + 1 - (x' + 1)
    have h1 : x' ≤ y + 1 := by omega
    rw [ih h1]
    change H5_a (y + 1 - x') x' = y + 1 - (x' + 1)
    have h2 : y + 1 - x' > 0 := by omega
    have h3 : ∃ k, y + 1 - x' = k + 1 := by use (y + 1 - x' - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y + 1 - (x' + 1)
    omega

lemma H5_comp (x : Nat) : evalPRF holdout_5 (fun _ => x) = evalPRF H5_c_prf (mk_args2 ((evalPRF H5_sub_1_prf (fun _ => x))) (x + 1)) := by
  change evalPRF H5_c_prf (fun j => evalPRFList prf_list![H5_sub_1_prf, PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_5_diverges : ∀ x, evalPRF holdout_5 (fun _ => x) > 0 := by
  intro x
  rw [H5_comp x]
  rw [H5_sub_1_val]
  unfold H5_sub_1
  rw [H5_c_val]
  rw [H5_c_cf _ _ (by omega)]
  omega

-- Translating holdout_6
-- M(C(R(P(2,1),R(P(3,1),R(R(P(3,3),P(5,1)),P(6,2)))),P(1,1),S,P(1,1)))
def HOLDOUT_6_p1 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨2, by decide⟩) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_6_p2 : PRF 5 := PRF.primRec HOLDOUT_6_p1 (PRF.proj 6 ⟨1, by decide⟩)
def HOLDOUT_6_p3 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨0, by decide⟩) HOLDOUT_6_p2
def HOLDOUT_6_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_6_p3
def HOLDOUT_6_p5 : PRF 1 := PRF.comp HOLDOUT_6_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_6 : PRF 1 := HOLDOUT_6_p5

theorem holdout_6_diverges : ∀ x, evalPRF holdout_6 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_7
-- M(C(R(P(2,1),R(R(P(2,1),R(P(3,3),P(5,1))),P(5,2))),S,S,S))
def HOLDOUT_7_p1 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨2, by decide⟩) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_7_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_7_p1
def HOLDOUT_7_p3 : PRF 4 := PRF.primRec HOLDOUT_7_p2 (PRF.proj 5 ⟨1, by decide⟩)
def HOLDOUT_7_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_7_p3
def HOLDOUT_7_p5 : PRF 1 := PRF.comp HOLDOUT_7_p4 prf_list![PRF.succ, PRF.succ, PRF.succ]
def holdout_7 : PRF 1 := HOLDOUT_7_p5

theorem holdout_7_diverges : ∀ x, evalPRF holdout_7 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_8
-- M(C(R(P(2,1),R(R(P(2,2),R(Z3,P(5,1))),P(5,2))),S,P(1,1),S))
def HOLDOUT_8_p1 : PRF 4 := PRF.primRec (PRF.zero 3) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_8_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_8_p1
def HOLDOUT_8_p3 : PRF 4 := PRF.primRec HOLDOUT_8_p2 (PRF.proj 5 ⟨1, by decide⟩)
def HOLDOUT_8_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_8_p3
def HOLDOUT_8_p5 : PRF 1 := PRF.comp HOLDOUT_8_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_8 : PRF 1 := HOLDOUT_8_p5

theorem holdout_8_diverges : ∀ x, evalPRF holdout_8 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_9
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,1),P(5,1))),P(5,2))),S,S,S))
def HOLDOUT_9_p1 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨0, by decide⟩) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_9_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_9_p1
def HOLDOUT_9_p3 : PRF 4 := PRF.primRec HOLDOUT_9_p2 (PRF.proj 5 ⟨1, by decide⟩)
def HOLDOUT_9_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_9_p3
def HOLDOUT_9_p5 : PRF 1 := PRF.comp HOLDOUT_9_p4 prf_list![PRF.succ, PRF.succ, PRF.succ]
def holdout_9 : PRF 1 := HOLDOUT_9_p5

theorem holdout_9_diverges : ∀ x, evalPRF holdout_9 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_10
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,P(1,1),S))
def HOLDOUT_10_p1 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨1, by decide⟩) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_10_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_10_p1
def HOLDOUT_10_p3 : PRF 4 := PRF.primRec HOLDOUT_10_p2 (PRF.proj 5 ⟨1, by decide⟩)
def HOLDOUT_10_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_10_p3
def HOLDOUT_10_p5 : PRF 1 := PRF.comp HOLDOUT_10_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_10 : PRF 1 := HOLDOUT_10_p5

theorem holdout_10_diverges : ∀ x, evalPRF holdout_10 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_11
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,S,P(1,1)))
def HOLDOUT_11_p1 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨1, by decide⟩) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_11_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_11_p1
def HOLDOUT_11_p3 : PRF 4 := PRF.primRec HOLDOUT_11_p2 (PRF.proj 5 ⟨1, by decide⟩)
def HOLDOUT_11_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_11_p3
def HOLDOUT_11_p5 : PRF 1 := PRF.comp HOLDOUT_11_p4 prf_list![PRF.succ, PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_11 : PRF 1 := HOLDOUT_11_p5

theorem holdout_11_diverges : ∀ x, evalPRF holdout_11 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_12
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,S,S))
def HOLDOUT_12_p1 : PRF 4 := PRF.primRec (PRF.proj 3 ⟨1, by decide⟩) (PRF.proj 5 ⟨0, by decide⟩)
def HOLDOUT_12_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_12_p1
def HOLDOUT_12_p3 : PRF 4 := PRF.primRec HOLDOUT_12_p2 (PRF.proj 5 ⟨1, by decide⟩)
def HOLDOUT_12_p4 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_12_p3
def HOLDOUT_12_p5 : PRF 1 := PRF.comp HOLDOUT_12_p4 prf_list![PRF.succ, PRF.succ, PRF.succ]
def holdout_12 : PRF 1 := HOLDOUT_12_p5

theorem holdout_12_diverges : ∀ x, evalPRF holdout_12 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 13
-- M(C(R(Z1,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_13 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

def H13_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H13_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H13_c_prf : PRF 2 := (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H13_a (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H13_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H13_c (x y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => H13_a (H13_c x' y) (H13_b x' (H13_c x' y) y)

lemma H13_a_val (x y : Nat) : evalPRF H13_a_prf (mk_args2 x y) = H13_a x y := by
  induction x <;> rfl

lemma H13_b_val (x _acc y : Nat) : evalPRF H13_b_prf (mk_args3 x _acc y) = H13_b x _acc y := by
  induction x <;> rfl

lemma H13_c_val (x y : Nat) : evalPRF H13_c_prf (mk_args2 x y) = H13_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H13_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H13_b_prf]) (mk_args3 x (evalPRF H13_c_prf (mk_args2 x y)) y) = H13_c (x + 1) y
    rw [ih]
    change evalPRF H13_a_prf (mk_args2 (H13_c x y) (evalPRF H13_b_prf (mk_args3 x (H13_c x y) y))) = H13_a (H13_c x y) (H13_b x (H13_c x y) y)
    rw [H13_b_val, H13_a_val]

lemma H13_comp (x : Nat) : evalPRF holdout_13 (fun _ => x) = evalPRF H13_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H13_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H13_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

lemma H13_c_cf (x0 y0 : Nat) (h : x0 ≤ y0) (h_pos : x0 > 0) : H13_c x0 y0 = y0 - x0 + 1 := by
  induction x0 with
  | zero => contradiction
  | succ x' ih =>
    cases x' with
    | zero =>
      change H13_a 0 _ = _
      change y0 = _
      omega
    | succ x'' =>
      have h1 : x'' + 1 ≤ y0 := by omega
      have hpos1 : x'' + 1 > 0 := by omega
      have ih_val := ih h1 hpos1
      change H13_a (H13_c (x'' + 1) y0) (H13_b (x'' + 1) (H13_c (x'' + 1) y0) y0) = _
      rw [ih_val]
      dsimp [H13_b]
      have h3 : ∃ k, y0 - (x'' + 1) + 1 = k + 1 := ⟨y0 - (x'' + 1), rfl⟩
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change k = _
      omega

theorem holdout_13_diverges : ∀ x, evalPRF holdout_13 (fun _ => x) > 0 := by
  intro x
  rw [H13_comp x]
  rw [H13_c_val]
  rw [H13_c_cf (x + 1) (x + 1) (by omega) (by omega)]
  omega


-- Translating holdout_14
-- M(C(R(Z1,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,P(1,1)))
def HOLDOUT_14_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_14_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def HOLDOUT_14_p3 : PRF 3 := PRF.comp HOLDOUT_14_p1 prf_list![(PRF.proj 3 ⟨1, by decide⟩), HOLDOUT_14_p2]
def HOLDOUT_14_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_14_p3
def HOLDOUT_14_p5 : PRF 1 := PRF.comp HOLDOUT_14_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_14 : PRF 1 := HOLDOUT_14_p5

theorem holdout_14_diverges : ∀ x, evalPRF holdout_14 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 15
-- M(C(R(Z1,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_15 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

def H15_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H15_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H15_c_prf : PRF 2 := (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H15_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H15_b (x _acc y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => x'

def H15_c (x y : Nat) : Nat :=
  match x with
  | 0 => 0
  | x' + 1 => H15_a (H15_c x' y) (H15_b x' (H15_c x' y) y)

lemma H15_a_val (x y : Nat) : evalPRF H15_a_prf (mk_args2 x y) = H15_a x y := by
  induction x <;> rfl

lemma H15_b_val (x _acc y : Nat) : evalPRF H15_b_prf (mk_args3 x _acc y) = H15_b x _acc y := by
  induction x <;> rfl

lemma H15_c_val (x y : Nat) : evalPRF H15_c_prf (mk_args2 x y) = H15_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H15_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H15_b_prf]) (mk_args3 x (evalPRF H15_c_prf (mk_args2 x y)) y) = H15_c (x + 1) y
    rw [ih]
    change evalPRF H15_a_prf (mk_args2 (H15_c x y) (evalPRF H15_b_prf (mk_args3 x (H15_c x y) y))) = H15_a (H15_c x y) (H15_b x (H15_c x y) y)
    rw [H15_b_val, H15_a_val]

lemma H15_comp (x : Nat) : evalPRF holdout_15 (fun _ => x) = evalPRF H15_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H15_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H15_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

lemma H15_c_cf (x0 y0 : Nat) (h : x0 ≤ y0 + 1) (h_pos : x0 > 0) : H15_c x0 y0 = y0 + 1 - x0 + 1 := by
  induction x0 with
  | zero => contradiction
  | succ x' ih =>
    cases x' with
    | zero =>
      change H15_a 0 _ = _
      change y0 + 1 = _
      omega
    | succ x'' =>
      have h1 : x'' + 1 ≤ y0 + 1 := by omega
      have hpos1 : x'' + 1 > 0 := by omega
      have ih_val := ih h1 hpos1
      change H15_a (H15_c (x'' + 1) y0) (H15_b (x'' + 1) (H15_c (x'' + 1) y0) y0) = _
      rw [ih_val]
      dsimp [H15_b]
      have h3 : ∃ k, y0 + 1 - (x'' + 1) + 1 = k + 1 := ⟨y0 + 1 - (x'' + 1), rfl⟩
      rcases h3 with ⟨k, hk⟩
      rw [hk]
      change k = _
      omega

theorem holdout_15_diverges : ∀ x, evalPRF holdout_15 (fun _ => x) > 0 := by
  intro x
  rw [H15_comp x]
  rw [H15_c_val]
  rw [H15_c_cf (x + 1) (x + 1) (by omega) (by omega)]
  omega


-- Translating holdout_16
-- M(C(R(Z1,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def HOLDOUT_16_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_16_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨2, by decide⟩)
def HOLDOUT_16_p3 : PRF 3 := PRF.comp HOLDOUT_16_p1 prf_list![HOLDOUT_16_p2, (PRF.proj 3 ⟨0, by decide⟩)]
def HOLDOUT_16_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_16_p3
def HOLDOUT_16_p5 : PRF 1 := PRF.comp HOLDOUT_16_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_16 : PRF 1 := HOLDOUT_16_p5

theorem holdout_16_diverges : ∀ x, evalPRF holdout_16 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_17
-- M(C(R(Z1,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),S,S))
def HOLDOUT_17_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_17_p2 : PRF 4 := PRF.comp HOLDOUT_17_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_17_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_17_p2
def HOLDOUT_17_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_17_p3
def HOLDOUT_17_p5 : PRF 1 := PRF.comp HOLDOUT_17_p4 prf_list![PRF.succ, PRF.succ]
def holdout_17 : PRF 1 := HOLDOUT_17_p5

theorem holdout_17_diverges : ∀ x, evalPRF holdout_17 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_18
-- M(C(R(Z1,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_18_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_18_p2 : PRF 4 := PRF.comp HOLDOUT_18_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_18_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_18_p2
def HOLDOUT_18_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_18_p3
def HOLDOUT_18_p5 : PRF 1 := PRF.comp HOLDOUT_18_p4 prf_list![PRF.succ, PRF.succ]
def holdout_18 : PRF 1 := HOLDOUT_18_p5

theorem holdout_18_diverges : ∀ x, evalPRF holdout_18 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_19
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),S,S))
def HOLDOUT_19_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_19_p2 : PRF 4 := PRF.comp HOLDOUT_19_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_19_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_19_p2
def HOLDOUT_19_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_19_p3
def HOLDOUT_19_p5 : PRF 1 := PRF.comp HOLDOUT_19_p4 prf_list![PRF.succ, PRF.succ]
def holdout_19 : PRF 1 := HOLDOUT_19_p5

theorem holdout_19_diverges : ∀ x, evalPRF holdout_19 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_20
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def HOLDOUT_20_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_20_p2 : PRF 4 := PRF.comp HOLDOUT_20_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]
def HOLDOUT_20_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_20_p2
def HOLDOUT_20_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_20_p3
def HOLDOUT_20_p5 : PRF 1 := PRF.comp HOLDOUT_20_p4 prf_list![PRF.succ, PRF.succ]
def holdout_20 : PRF 1 := HOLDOUT_20_p5

theorem holdout_20_diverges : ∀ x, evalPRF holdout_20 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_21
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_21_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_21_p2 : PRF 4 := PRF.comp HOLDOUT_21_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_21_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_21_p2
def HOLDOUT_21_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_21_p3
def HOLDOUT_21_p5 : PRF 1 := PRF.comp HOLDOUT_21_p4 prf_list![PRF.succ, PRF.succ]
def holdout_21 : PRF 1 := HOLDOUT_21_p5

theorem holdout_21_diverges : ∀ x, evalPRF holdout_21 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_22
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def HOLDOUT_22_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_22_p2 : PRF 4 := PRF.comp HOLDOUT_22_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_22_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_22_p2
def HOLDOUT_22_p4 : PRF 2 := PRF.primRec (PRF.zero 1) HOLDOUT_22_p3
def HOLDOUT_22_p5 : PRF 1 := PRF.comp HOLDOUT_22_p4 prf_list![PRF.succ, PRF.succ]
def holdout_22 : PRF 1 := HOLDOUT_22_p5

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

def H23_b (x _acc _y : Nat) : Nat :=
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

def H25_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H25_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H25_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)]))

def H25_a (x y : Nat) : Nat := match x with
  | 0 => y
  | x' + 1 => x'
def H25_b (x _acc _y : Nat) : Nat := x

lemma H25_a_val (x y : Nat) : evalPRF H25_a_prf (mk_args2 x y) = H25_a x y := by
  cases x <;> rfl

lemma H25_b_val (x acc y : Nat) : evalPRF H25_b_prf (mk_args3 x acc y) = H25_b x acc y := by
  rfl

def H25_acc_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩))
def H25_acc (x acc y : Nat) : Nat := match x with | 0 => y | _ + 1 => acc
lemma H25_acc_val (x acc y : Nat) : evalPRF H25_acc_prf (mk_args3 x acc y) = H25_acc x acc y := by
  cases x <;> rfl

def H25_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H25_a (H25_acc x' (H25_c x' y) y) (H25_b x' (H25_c x' y) y)

lemma H25_c_val (x y : Nat) : evalPRF H25_c_prf (mk_args2 x y) = H25_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
--     change evalPRF H25_c_prf (mk_args2 (x' + 1) y) = H25_c (x' + 1) y
    have h_eval : evalPRF H25_c_prf (mk_args2 (x' + 1) y) = evalPRF H25_a_prf (mk_args2 (evalPRF H25_acc_prf (mk_args3 x' (evalPRF H25_c_prf (mk_args2 x' y)) y)) (evalPRF H25_b_prf (mk_args3 x' (evalPRF H25_c_prf (mk_args2 x' y)) y))) := by rfl
    rw [h_eval, H25_acc_val, H25_b_val]
    rw [H25_a_val, ih]
    rfl


lemma H25_c_cf_succ (x y : Nat) (h : x + 1 ≤ y) : H25_c (x + 1) y = y - (x + 1) := by
  induction x with
  | zero =>
    change H25_a y 0 = y - 1
    have hy : y > 0 := by omega
    have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = k + 1 - 1
    omega
  | succ x' ih =>
    have ih_val := ih (by omega)
    change H25_a (H25_c (x' + 1) y) (x' + 1) = y - (x' + 2)
    rw [ih_val]
--     change H25_a (y - (x' + 1)) (x' + 1) = y - (x' + 2)
    have hz : y - (x' + 1) > 0 := by omega
    have h3 : ∃ k, y - (x' + 1) = k + 1 := by use (y - (x' + 1) - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y - (x' + 2)
    omega

lemma H25_comp (x : Nat) : evalPRF holdout_25 (fun _ => x) = evalPRF H25_c_prf (mk_args2 (x) (x + 1)) := by
  change evalPRF H25_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_25_diverges : ∀ x, evalPRF holdout_25 (fun _ => x) > 0 := by
  intro x
  rw [H25_comp x]
  rw [H25_c_val]
  cases h : x with
  | zero =>
    dsimp [H25_c]
    omega
  | succ x' =>
    rw [H25_c_cf_succ _ _ (by omega)]
    omega

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

def H26_b (x _acc _y : Nat) : Nat :=
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

def H27_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H27_b_prf : PRF 3 := PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))
def H27_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H27_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H27_b (x acc y : Nat) : Nat :=
  evalPRF H27_b_prf (mk_args3 x acc y)

lemma H27_a_val (x y : Nat) : evalPRF H27_a_prf (mk_args2 x y) = H27_a x y := by
  induction x <;> rfl

def H27_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H27_a (H27_c x' y) (H27_b x' (H27_c x' y) y)

lemma H27_c_val (x y : Nat) : evalPRF H27_c_prf (mk_args2 x y) = H27_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H27_a_prf (mk_args2 (evalPRF H27_c_prf (mk_args2 x' y)) (evalPRF H27_b_prf (mk_args3 x' (evalPRF H27_c_prf (mk_args2 x' y)) y))) = H27_a (H27_c x' y) (H27_b x' (H27_c x' y) y)
    rw [ih]
    rw [H27_a_val]
    rfl

lemma H27_c_cf (x y : Nat) (h : x < y + 0) (hx : x > 0) : H27_c x y = y + 0 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H27_a (H27_c x y) (H27_b x (H27_c x y) y) = y + 0 - (x + 1)
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
      change H27_a (k + 1) (H27_b x (k + 1) y) = y + 0 - (x + 1)
      change k = y + 0 - (x + 1)
      omega

lemma H27_c_diag (x : Nat) : H27_c x x = 0 := by
  cases x with
  | zero => rfl
  | succ x' =>
    change H27_a (H27_c x' (x' + 1)) (H27_b x' (H27_c x' (x' + 1)) (x' + 1)) = 0
    have hcases : x' = 0 ∨ x' > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x' < (x' + 1) + 0 := by omega
      rw [H27_c_cf x' (x' + 1) h1 hpos]
      have h3 : (x' + 1) + 0 - x' = 1 := by omega
      rw [h3]
      rfl

lemma H27_comp (x : Nat) : evalPRF holdout_27 (fun _ => x) = evalPRF H27_c_prf (mk_args2 (x+1) x) := by
  change evalPRF H27_c_prf (fun j => evalPRFList prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H27_c_prf (mk_args2 (x+1) x)
  apply congrArg (evalPRF H27_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_27_diverges : ∀ x, evalPRF holdout_27 (fun _ => x) > 0 := by
  intro x
  rw [H27_comp x]
  cases x with
  | zero =>
    change evalPRF H27_c_prf (mk_args2 1 0) > 0
    rw [H27_c_val]
    decide
  | succ x' =>
    change evalPRF H27_c_prf (mk_args2 (x'+2) (x'+1)) > 0
    rw [H27_c_val]
    have h_diag := H27_c_diag (x' + 1)
    change H27_a (H27_c (x' + 1) (x' + 1)) (H27_b (x' + 1) (H27_c (x' + 1) (x' + 1)) (x' + 1)) > 0
    rw [h_diag]
    change H27_b (x' + 1) 0 (x' + 1) + 1 > 0
    omega

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

def H29_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H29_b_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))
def H29_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))]))

def H29_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

def H29_b (x acc y : Nat) : Nat :=
  evalPRF H29_b_prf (mk_args3 x acc y)

lemma H29_a_val (x y : Nat) : evalPRF H29_a_prf (mk_args2 x y) = H29_a x y := by
  induction x <;> rfl

def H29_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H29_a (H29_c x' y) (H29_b x' (H29_c x' y) y)

lemma H29_c_val (x y : Nat) : evalPRF H29_c_prf (mk_args2 x y) = H29_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H29_a_prf (mk_args2 (evalPRF H29_c_prf (mk_args2 x' y)) (evalPRF H29_b_prf (mk_args3 x' (evalPRF H29_c_prf (mk_args2 x' y)) y))) = H29_a (H29_c x' y) (H29_b x' (H29_c x' y) y)
    rw [ih]
    rw [H29_a_val]
    rfl

lemma H29_c_cf (x y : Nat) (h : x < y + 0) (hx : x > 0) : H29_c x y = y + 0 - x := by
  induction x with
  | zero => contradiction
  | succ x ih =>
    change H29_a (H29_c x y) (H29_b x (H29_c x y) y) = y + 0 - (x + 1)
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
      change H29_a (k + 1) (H29_b x (k + 1) y) = y + 0 - (x + 1)
      change k = y + 0 - (x + 1)
      omega

lemma H29_c_diag (x : Nat) : H29_c x x = 0 := by
  cases x with
  | zero => rfl
  | succ x' =>
    change H29_a (H29_c x' (x' + 1)) (H29_b x' (H29_c x' (x' + 1)) (x' + 1)) = 0
    have hcases : x' = 0 ∨ x' > 0 := by omega
    cases hcases with
    | inl h0 =>
      rw [h0]
      rfl
    | inr hpos =>
      have h1 : x' < (x' + 1) + 0 := by omega
      rw [H29_c_cf x' (x' + 1) h1 hpos]
      have h3 : (x' + 1) + 0 - x' = 1 := by omega
      rw [h3]
      rfl

lemma H29_comp (x : Nat) : evalPRF holdout_29 (fun _ => x) = evalPRF H29_c_prf (mk_args2 (x+1) x) := by
  change evalPRF H29_c_prf (fun j => evalPRFList prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)] j (fun _ => x)) = evalPRF H29_c_prf (mk_args2 (x+1) x)
  apply congrArg (evalPRF H29_c_prf)
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_29_diverges : ∀ x, evalPRF holdout_29 (fun _ => x) > 0 := by
  intro x
  rw [H29_comp x]
  cases x with
  | zero =>
    change evalPRF H29_c_prf (mk_args2 1 0) > 0
    rw [H29_c_val]
    decide
  | succ x' =>
    change evalPRF H29_c_prf (mk_args2 (x'+2) (x'+1)) > 0
    rw [H29_c_val]
    have h_diag := H29_c_diag (x' + 1)
    change H29_a (H29_c (x' + 1) (x' + 1)) (H29_b (x' + 1) (H29_c (x' + 1) (x' + 1)) (x' + 1)) > 0
    rw [h_diag]
    change H29_b (x' + 1) 0 (x' + 1) + 1 > 0
    omega

-- Translating holdout 30
-- M(C(R(P(1,1),C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_30 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

def H30_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H30_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H30_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)]))

def H30_a (x y : Nat) : Nat := match x with
  | 0 => y + 1
  | x' + 1 => x'
def H30_b (x _acc _y : Nat) : Nat := x

lemma H30_a_val (x y : Nat) : evalPRF H30_a_prf (mk_args2 x y) = H30_a x y := by
  cases x <;> rfl

lemma H30_b_val (x acc y : Nat) : evalPRF H30_b_prf (mk_args3 x acc y) = H30_b x acc y := by
  rfl

def H30_acc_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩))
def H30_acc (x acc y : Nat) : Nat := match x with | 0 => y | _ + 1 => acc
lemma H30_acc_val (x acc y : Nat) : evalPRF H30_acc_prf (mk_args3 x acc y) = H30_acc x acc y := by
  cases x <;> rfl

def H30_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H30_a (H30_acc x' (H30_c x' y) y) (H30_b x' (H30_c x' y) y)

lemma H30_c_val (x y : Nat) : evalPRF H30_c_prf (mk_args2 x y) = H30_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
--     change evalPRF H30_c_prf (mk_args2 (x' + 1) y) = H30_c (x' + 1) y
    have h_eval : evalPRF H30_c_prf (mk_args2 (x' + 1) y) = evalPRF H30_a_prf (mk_args2 (evalPRF H30_acc_prf (mk_args3 x' (evalPRF H30_c_prf (mk_args2 x' y)) y)) (evalPRF H30_b_prf (mk_args3 x' (evalPRF H30_c_prf (mk_args2 x' y)) y))) := by rfl
    rw [h_eval, H30_acc_val, H30_b_val]
    rw [H30_a_val, ih]
    rfl


lemma H30_c_cf_succ (x y : Nat) (h : x + 1 ≤ y) : H30_c (x + 1) y = y - (x + 1) := by
  induction x with
  | zero =>
    change H30_a y 0 = y - 1
    have hy : y > 0 := by omega
    have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = k + 1 - 1
    omega
  | succ x' ih =>
    have ih_val := ih (by omega)
    change H30_a (H30_c (x' + 1) y) (x' + 1) = y - (x' + 2)
    rw [ih_val]
--     change H30_a (y - (x' + 1)) (x' + 1) = y - (x' + 2)
    have hz : y - (x' + 1) > 0 := by omega
    have h3 : ∃ k, y - (x' + 1) = k + 1 := by use (y - (x' + 1) - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y - (x' + 2)
    omega

lemma H30_comp (x : Nat) : evalPRF holdout_30 (fun _ => x) = evalPRF H30_c_prf (mk_args2 (x) (x + 1)) := by
  change evalPRF H30_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_30_diverges : ∀ x, evalPRF holdout_30 (fun _ => x) > 0 := by
  intro x
  rw [H30_comp x]
  rw [H30_c_val]
  cases h : x with
  | zero =>
    dsimp [H30_c]
    omega
  | succ x' =>
    rw [H30_c_cf_succ _ _ (by omega)]
    omega

-- Translating holdout_31
-- M(C(R(P(1,1),C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def HOLDOUT_31_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_31_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨2, by decide⟩)
def HOLDOUT_31_p3 : PRF 3 := PRF.comp HOLDOUT_31_p1 prf_list![HOLDOUT_31_p2, (PRF.proj 3 ⟨0, by decide⟩)]
def HOLDOUT_31_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_31_p3
def HOLDOUT_31_p5 : PRF 1 := PRF.comp HOLDOUT_31_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_31 : PRF 1 := HOLDOUT_31_p5

theorem holdout_31_diverges : ∀ x, evalPRF holdout_31 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_32
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,Z1))
def HOLDOUT_32_p1 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def HOLDOUT_32_p2 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_32_p1
def HOLDOUT_32_p3 : PRF 3 := PRF.comp HOLDOUT_32_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.zero 3)]
def HOLDOUT_32_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_32_p3
def HOLDOUT_32_p5 : PRF 1 := PRF.comp HOLDOUT_32_p4 prf_list![PRF.succ, (PRF.zero 1)]
def holdout_32 : PRF 1 := HOLDOUT_32_p5

theorem holdout_32_diverges : ∀ x, evalPRF holdout_32 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_33
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,P(1,1)))
def HOLDOUT_33_p1 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def HOLDOUT_33_p2 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_33_p1
def HOLDOUT_33_p3 : PRF 3 := PRF.comp HOLDOUT_33_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.zero 3)]
def HOLDOUT_33_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_33_p3
def HOLDOUT_33_p5 : PRF 1 := PRF.comp HOLDOUT_33_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_33 : PRF 1 := HOLDOUT_33_p5

theorem holdout_33_diverges : ∀ x, evalPRF holdout_33 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 34
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,S))
def holdout_34 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.succ]

def H34_a_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))))
def H34_b_prf : PRF 3 := PRF.zero 3
def H34_c_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3]))

def H34_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | 1 => y + 1
  | x' + 2 => x'

def H34_b (_x _acc _y : Nat) : Nat := 0

def H34_c (x y : Nat) : Nat :=
  match x with
  | 0 => y
  | x' + 1 => H34_a (H34_c x' y) (H34_b x' (H34_c x' y) y)

def H34_aux (x y : Nat) : Nat :=
  if 2 * x > y then 1 else if 2 * x = y then 0 else y - 2 * x

lemma H34_a_val (x y : Nat) : evalPRF H34_a_prf (mk_args2 x y) = H34_a x y := by
  match x with | 0 => rfl | 1 => rfl | x' + 2 => rfl

lemma H34_b_val (x _acc y : Nat) : evalPRF H34_b_prf (mk_args3 x _acc y) = H34_b x _acc y := by
  rfl

lemma H34_c_val (x y : Nat) : evalPRF H34_c_prf (mk_args2 x y) = H34_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H34_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H34_b_prf]) (mk_args3 x (evalPRF H34_c_prf (mk_args2 x y)) y) = H34_c (x + 1) y
    rw [ih]
    change evalPRF H34_a_prf (mk_args2 (H34_c x y) (evalPRF H34_b_prf (mk_args3 x (H34_c x y) y))) = H34_a (H34_c x y) (H34_b x (H34_c x y) y)
    rw [H34_b_val, H34_a_val]

lemma H34_comp (x : Nat) : evalPRF holdout_34 (fun _ => x) = evalPRF H34_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H34_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H34_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

lemma H34_c_cf (x0 y0 : Nat) : H34_c x0 y0 = H34_aux x0 y0 := by
  induction x0 with
  | zero =>
    unfold H34_c H34_aux
    repeat (first | split | rfl | omega)
  | succ x' ih =>
    unfold H34_c H34_b H34_aux
    rw [ih]
    unfold H34_aux
    repeat (
      first
      | split
      | rfl
      | omega
      | have h : y0 - 2 * x' = 1 := by omega
        rw [h]
        rfl
      | have h : y0 - 2 * x' = 2 := by omega
        rw [h]
        rfl
      | have h : ∃ k, y0 - 2 * x' = k + 2 := ⟨y0 - 2 * x' - 2, by omega⟩
        rcases h with ⟨k, hk⟩
        rw [hk]
        dsimp [H34_a]
        omega
    )

theorem holdout_34_diverges : ∀ x, evalPRF holdout_34 (fun _ => x) > 0 := by
  intro x
  rw [H34_comp x]
  rw [H34_c_val]
  rw [H34_c_cf]
  unfold H34_aux
  have h : 2 * (x + 1) > x + 1 := by omega
  simp only [if_pos h]
  omega

-- Translating holdout_35
-- M(C(R(P(1,1),C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),S))
def HOLDOUT_35_p1 : PRF 1 := PRF.primRec (PRF.zero 0) (PRF.proj 2 ⟨0, by decide⟩)
def HOLDOUT_35_p2 : PRF 2 := PRF.primRec HOLDOUT_35_p1 (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_35_p3 : PRF 3 := PRF.comp HOLDOUT_35_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]
def HOLDOUT_35_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_35_p3
def HOLDOUT_35_p5 : PRF 1 := PRF.comp HOLDOUT_35_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_35 : PRF 1 := HOLDOUT_35_p5

theorem holdout_35_diverges : ∀ x, evalPRF holdout_35 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_36
-- M(C(R(P(1,1),R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_36_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_36_p2 : PRF 4 := PRF.comp HOLDOUT_36_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_36_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_36_p2
def HOLDOUT_36_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_36_p3
def HOLDOUT_36_p5 : PRF 1 := PRF.comp HOLDOUT_36_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_36 : PRF 1 := HOLDOUT_36_p5

theorem holdout_36_diverges : ∀ x, evalPRF holdout_36 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_37
-- M(C(R(P(1,1),R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_37_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_37_p2 : PRF 4 := PRF.comp HOLDOUT_37_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_37_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_37_p2
def HOLDOUT_37_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_37_p3
def HOLDOUT_37_p5 : PRF 1 := PRF.comp HOLDOUT_37_p4 prf_list![PRF.succ, PRF.succ]
def holdout_37 : PRF 1 := HOLDOUT_37_p5

theorem holdout_37_diverges : ∀ x, evalPRF holdout_37 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_38
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_38_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_38_p2 : PRF 4 := PRF.comp HOLDOUT_38_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_38_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_38_p2
def HOLDOUT_38_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_38_p3
def HOLDOUT_38_p5 : PRF 1 := PRF.comp HOLDOUT_38_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_38 : PRF 1 := HOLDOUT_38_p5

theorem holdout_38_diverges : ∀ x, evalPRF holdout_38 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_39
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_39_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_39_p2 : PRF 4 := PRF.comp HOLDOUT_39_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_39_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_39_p2
def HOLDOUT_39_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_39_p3
def HOLDOUT_39_p5 : PRF 1 := PRF.comp HOLDOUT_39_p4 prf_list![PRF.succ, PRF.succ]
def holdout_39 : PRF 1 := HOLDOUT_39_p5

theorem holdout_39_diverges : ∀ x, evalPRF holdout_39 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_40
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def HOLDOUT_40_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_40_p2 : PRF 4 := PRF.comp HOLDOUT_40_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_40_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_40_p2
def HOLDOUT_40_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_40_p3
def HOLDOUT_40_p5 : PRF 1 := PRF.comp HOLDOUT_40_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_40 : PRF 1 := HOLDOUT_40_p5

theorem holdout_40_diverges : ∀ x, evalPRF holdout_40 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_41
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def HOLDOUT_41_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_41_p2 : PRF 4 := PRF.comp HOLDOUT_41_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_41_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_41_p2
def HOLDOUT_41_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_41_p3
def HOLDOUT_41_p5 : PRF 1 := PRF.comp HOLDOUT_41_p4 prf_list![PRF.succ, PRF.succ]
def holdout_41 : PRF 1 := HOLDOUT_41_p5

theorem holdout_41_diverges : ∀ x, evalPRF holdout_41 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_42
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def HOLDOUT_42_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_42_p2 : PRF 4 := PRF.comp HOLDOUT_42_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_42_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_42_p2
def HOLDOUT_42_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_42_p3
def HOLDOUT_42_p5 : PRF 1 := PRF.comp HOLDOUT_42_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_42 : PRF 1 := HOLDOUT_42_p5

theorem holdout_42_diverges : ∀ x, evalPRF holdout_42 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_43
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_43_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_43_p2 : PRF 4 := PRF.comp HOLDOUT_43_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_43_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_43_p2
def HOLDOUT_43_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_43_p3
def HOLDOUT_43_p5 : PRF 1 := PRF.comp HOLDOUT_43_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_43 : PRF 1 := HOLDOUT_43_p5

theorem holdout_43_diverges : ∀ x, evalPRF holdout_43 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_44
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_44_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_44_p2 : PRF 4 := PRF.comp HOLDOUT_44_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_44_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_44_p2
def HOLDOUT_44_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_44_p3
def HOLDOUT_44_p5 : PRF 1 := PRF.comp HOLDOUT_44_p4 prf_list![PRF.succ, PRF.succ]
def holdout_44 : PRF 1 := HOLDOUT_44_p5

theorem holdout_44_diverges : ∀ x, evalPRF holdout_44 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_45
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def HOLDOUT_45_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_45_p2 : PRF 4 := PRF.comp HOLDOUT_45_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_45_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_45_p2
def HOLDOUT_45_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_45_p3
def HOLDOUT_45_p5 : PRF 1 := PRF.comp HOLDOUT_45_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_45 : PRF 1 := HOLDOUT_45_p5

theorem holdout_45_diverges : ∀ x, evalPRF holdout_45 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_46
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),S))
def HOLDOUT_46_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_46_p2 : PRF 4 := PRF.comp HOLDOUT_46_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]
def HOLDOUT_46_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_46_p2
def HOLDOUT_46_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_46_p3
def HOLDOUT_46_p5 : PRF 1 := PRF.comp HOLDOUT_46_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_46 : PRF 1 := HOLDOUT_46_p5

theorem holdout_46_diverges : ∀ x, evalPRF holdout_46 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_47
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def HOLDOUT_47_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_47_p2 : PRF 4 := PRF.comp HOLDOUT_47_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]
def HOLDOUT_47_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_47_p2
def HOLDOUT_47_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_47_p3
def HOLDOUT_47_p5 : PRF 1 := PRF.comp HOLDOUT_47_p4 prf_list![PRF.succ, PRF.succ]
def holdout_47 : PRF 1 := HOLDOUT_47_p5

theorem holdout_47_diverges : ∀ x, evalPRF holdout_47 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_48
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_48_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_48_p2 : PRF 4 := PRF.comp HOLDOUT_48_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_48_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_48_p2
def HOLDOUT_48_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_48_p3
def HOLDOUT_48_p5 : PRF 1 := PRF.comp HOLDOUT_48_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_48 : PRF 1 := HOLDOUT_48_p5

theorem holdout_48_diverges : ∀ x, evalPRF holdout_48 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_49
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_49_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_49_p2 : PRF 4 := PRF.comp HOLDOUT_49_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_49_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_49_p2
def HOLDOUT_49_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_49_p3
def HOLDOUT_49_p5 : PRF 1 := PRF.comp HOLDOUT_49_p4 prf_list![PRF.succ, PRF.succ]
def holdout_49 : PRF 1 := HOLDOUT_49_p5

theorem holdout_49_diverges : ∀ x, evalPRF holdout_49 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_50
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def HOLDOUT_50_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_50_p2 : PRF 4 := PRF.comp HOLDOUT_50_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_50_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_50_p2
def HOLDOUT_50_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_50_p3
def HOLDOUT_50_p5 : PRF 1 := PRF.comp HOLDOUT_50_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_50 : PRF 1 := HOLDOUT_50_p5

theorem holdout_50_diverges : ∀ x, evalPRF holdout_50 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_51
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def HOLDOUT_51_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_51_p2 : PRF 4 := PRF.comp HOLDOUT_51_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_51_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_51_p2
def HOLDOUT_51_p4 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) HOLDOUT_51_p3
def HOLDOUT_51_p5 : PRF 1 := PRF.comp HOLDOUT_51_p4 prf_list![PRF.succ, PRF.succ]
def holdout_51 : PRF 1 := HOLDOUT_51_p5

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

def H52_b (x _acc _y : Nat) : Nat :=
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

def H53_b (x _acc _y : Nat) : Nat :=
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

def H54_b (x _acc _y : Nat) : Nat :=
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

def H58_a_prf : PRF 2 := (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩)))
def H58_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H58_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)]))

def H58_a (x y : Nat) : Nat := match x with
  | 0 => y
  | x' + 1 => x'
def H58_b (x _acc _y : Nat) : Nat := x

lemma H58_a_val (x y : Nat) : evalPRF H58_a_prf (mk_args2 x y) = H58_a x y := by
  cases x <;> rfl

lemma H58_b_val (x acc y : Nat) : evalPRF H58_b_prf (mk_args3 x acc y) = H58_b x acc y := by
  rfl

def H58_acc_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩))
def H58_acc (x acc y : Nat) : Nat := match x with | 0 => y | _ + 1 => acc
lemma H58_acc_val (x acc y : Nat) : evalPRF H58_acc_prf (mk_args3 x acc y) = H58_acc x acc y := by
  cases x <;> rfl

def H58_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H58_a (H58_acc x' (H58_c x' y) y) (H58_b x' (H58_c x' y) y)

lemma H58_c_val (x y : Nat) : evalPRF H58_c_prf (mk_args2 x y) = H58_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
--     change evalPRF H58_c_prf (mk_args2 (x' + 1) y) = H58_c (x' + 1) y
    have h_eval : evalPRF H58_c_prf (mk_args2 (x' + 1) y) = evalPRF H58_a_prf (mk_args2 (evalPRF H58_acc_prf (mk_args3 x' (evalPRF H58_c_prf (mk_args2 x' y)) y)) (evalPRF H58_b_prf (mk_args3 x' (evalPRF H58_c_prf (mk_args2 x' y)) y))) := by rfl
    rw [h_eval, H58_acc_val, H58_b_val]
    rw [H58_a_val, ih]
    rfl


lemma H58_c_cf_succ (x y : Nat) (h : x + 1 ≤ y) : H58_c (x + 1) y = y - (x + 1) := by
  induction x with
  | zero =>
    change H58_a y 0 = y - 1
    have hy : y > 0 := by omega
    have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = k + 1 - 1
    omega
  | succ x' ih =>
    have ih_val := ih (by omega)
    change H58_a (H58_c (x' + 1) y) (x' + 1) = y - (x' + 2)
    rw [ih_val]
--     change H58_a (y - (x' + 1)) (x' + 1) = y - (x' + 2)
    have hz : y - (x' + 1) > 0 := by omega
    have h3 : ∃ k, y - (x' + 1) = k + 1 := by use (y - (x' + 1) - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y - (x' + 2)
    omega

lemma H58_comp (x : Nat) : evalPRF holdout_58 (fun _ => x) = evalPRF H58_c_prf (mk_args2 (x) (x + 1)) := by
  change evalPRF H58_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_58_diverges : ∀ x, evalPRF holdout_58 (fun _ => x) > 0 := by
  intro x
  rw [H58_comp x]
  rw [H58_c_val]
  cases h : x with
  | zero =>
    dsimp [H58_c]
    omega
  | succ x' =>
    rw [H58_c_cf_succ _ _ (by omega)]
    omega

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

def H59_b (x _acc _y : Nat) : Nat :=
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

def H60_b (x _acc _y : Nat) : Nat :=
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

def H61_b (x _acc _y : Nat) : Nat :=
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

def H65_a_prf : PRF 2 := (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))
def H65_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H65_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)]))

def H65_a (x y : Nat) : Nat := match x with
  | 0 => y + 1
  | x' + 1 => x'
def H65_b (x _acc _y : Nat) : Nat := x

lemma H65_a_val (x y : Nat) : evalPRF H65_a_prf (mk_args2 x y) = H65_a x y := by
  cases x <;> rfl

lemma H65_b_val (x acc y : Nat) : evalPRF H65_b_prf (mk_args3 x acc y) = H65_b x acc y := by
  rfl

def H65_acc_prf : PRF 3 := PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩))
def H65_acc (x acc y : Nat) : Nat := match x with | 0 => y | _ + 1 => acc
lemma H65_acc_val (x acc y : Nat) : evalPRF H65_acc_prf (mk_args3 x acc y) = H65_acc x acc y := by
  cases x <;> rfl

def H65_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H65_a (H65_acc x' (H65_c x' y) y) (H65_b x' (H65_c x' y) y)

lemma H65_c_val (x y : Nat) : evalPRF H65_c_prf (mk_args2 x y) = H65_c x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
--     change evalPRF H65_c_prf (mk_args2 (x' + 1) y) = H65_c (x' + 1) y
    have h_eval : evalPRF H65_c_prf (mk_args2 (x' + 1) y) = evalPRF H65_a_prf (mk_args2 (evalPRF H65_acc_prf (mk_args3 x' (evalPRF H65_c_prf (mk_args2 x' y)) y)) (evalPRF H65_b_prf (mk_args3 x' (evalPRF H65_c_prf (mk_args2 x' y)) y))) := by rfl
    rw [h_eval, H65_acc_val, H65_b_val]
    rw [H65_a_val, ih]
    rfl


lemma H65_c_cf_succ (x y : Nat) (h : x + 1 ≤ y) : H65_c (x + 1) y = y - (x + 1) := by
  induction x with
  | zero =>
    change H65_a y 0 = y - 1
    have hy : y > 0 := by omega
    have h3 : ∃ k, y = k + 1 := by use (y - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = k + 1 - 1
    omega
  | succ x' ih =>
    have ih_val := ih (by omega)
    change H65_a (H65_c (x' + 1) y) (x' + 1) = y - (x' + 2)
    rw [ih_val]
--     change H65_a (y - (x' + 1)) (x' + 1) = y - (x' + 2)
    have hz : y - (x' + 1) > 0 := by omega
    have h3 : ∃ k, y - (x' + 1) = k + 1 := by use (y - (x' + 1) - 1); omega
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    change k = y - (x' + 2)
    omega

lemma H65_comp (x : Nat) : evalPRF holdout_65 (fun _ => x) = evalPRF H65_c_prf (mk_args2 (x) (x + 1)) := by
  change evalPRF H65_c_prf (fun j => evalPRFList prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ] j (fun _ => x)) = _
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

theorem holdout_65_diverges : ∀ x, evalPRF holdout_65 (fun _ => x) > 0 := by
  intro x
  rw [H65_comp x]
  rw [H65_c_val]
  cases h : x with
  | zero =>
    dsimp [H65_c]
    omega
  | succ x' =>
    rw [H65_c_cf_succ _ _ (by omega)]
    omega

-- Translating holdout_66
-- M(C(R(S,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def HOLDOUT_66_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_66_p2 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) (PRF.proj 4 ⟨2, by decide⟩)
def HOLDOUT_66_p3 : PRF 3 := PRF.comp HOLDOUT_66_p1 prf_list![HOLDOUT_66_p2, (PRF.proj 3 ⟨0, by decide⟩)]
def HOLDOUT_66_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_66_p3
def HOLDOUT_66_p5 : PRF 1 := PRF.comp HOLDOUT_66_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_66 : PRF 1 := HOLDOUT_66_p5

def h66_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => x'

lemma H66_p1_val (x y : Nat) : evalPRF HOLDOUT_66_p1 (mk_args2 x y) = h66_a x y := by
  cases x
  · rfl
  · rfl

def h66_b (x y z : Nat) : Nat :=
  match x with
  | 0 => z
  | x' + 1 => y

lemma H66_p2_val (x y z : Nat) : evalPRF HOLDOUT_66_p2 (mk_args3 x y z) = h66_b x y z := by
  cases x
  · rfl
  · rfl

def h66_c (x y z : Nat) : Nat :=
  match x, y, z with
  | 0, _, 0 => 1
  | 0, _, z'+1 => z'
  | x'+1, 0, _ => x' + 2
  | x'+1, y'+1, _ => y'

lemma H66_p3_val (x y z : Nat) : evalPRF HOLDOUT_66_p3 (mk_args3 x y z) = h66_c x y z := by
  change evalPRF HOLDOUT_66_p1 (mk_args2 (evalPRF HOLDOUT_66_p2 (mk_args3 x y z)) x) = h66_c x y z
  rw [H66_p2_val, H66_p1_val]
  unfold h66_a h66_b h66_c
  cases x
  · cases z
    · rfl
    · rfl
  · cases y
    · rfl
    · rfl

def h66_d (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => h66_c x' (h66_d x' y) y

lemma H66_p4_val (x y : Nat) : evalPRF HOLDOUT_66_p4 (mk_args2 x y) = h66_d x y := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF HOLDOUT_66_p3 (mk_args3 x' (evalPRF HOLDOUT_66_p4 (mk_args2 x' y)) y) = _
    rw [ih, H66_p3_val]
    rfl

lemma h66_d_lt (y x : Nat) : (x > 0) → (x ≤ y) → h66_d x y = y - x := by
  intro hx hle
  induction x with
  | zero => contradiction
  | succ x' ih =>
    unfold h66_d
    cases x' with
    | zero =>
      -- x = 1
      dsimp [h66_c]
      have hy : y > 0 := by omega
      cases y
      · contradiction
      · rfl
    | succ x'' =>
      -- x > 1
      have ih' := ih (by omega) (by omega)
      rw [ih']
      have hy : y - (x'' + 1) > 0 := by omega
      cases h_y : (y - (x'' + 1)) with
      | zero =>
        rw [h_y] at hy
        contradiction
      | succ n =>
        change h66_c (x''+1) (n + 1) y = y - (x'' + 2)
        dsimp [h66_c]
        omega

lemma h66_d_diag (x : Nat) : h66_d (x + 1) x = x + 1 := by
  cases x with
  | zero => rfl
  | succ x' =>
    unfold h66_d
    have hd := h66_d_lt (x' + 1) (x' + 1) (by omega) (by omega)
    rw [hd]
    have h_zero : x' + 1 - (x' + 1) = 0 := by omega
    rw [h_zero]
    change h66_c (x' + 1) 0 (x' + 1) = x' + 2
    rfl

theorem holdout_66_diverges : ∀ x, evalPRF holdout_66 (fun _ => x) > 0 := by
  intro x
  unfold holdout_66 HOLDOUT_66_p5
  change evalPRF HOLDOUT_66_p4 (mk_args2 (x + 1) x) > 0
  rw [H66_p4_val]
  rw [h66_d_diag]
  omega

-- Translating holdout_67
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),P(1,1),Z1))
def HOLDOUT_67_p1 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def HOLDOUT_67_p2 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_67_p1
def HOLDOUT_67_p3 : PRF 3 := PRF.comp HOLDOUT_67_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.zero 3)]
def HOLDOUT_67_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_67_p3
def HOLDOUT_67_p5 : PRF 1 := PRF.comp HOLDOUT_67_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.zero 1)]
def holdout_67 : PRF 1 := HOLDOUT_67_p5

theorem holdout_67_diverges : ∀ x, evalPRF holdout_67 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 68
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,Z1))
def holdout_68 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.zero 1]

def H68_a_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))))
def H68_b_prf : PRF 3 := PRF.zero 3
def H68_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3]))

def H68_a (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | 1 => y + 1
  | x' + 2 => x'

def H68_b (_x _acc _y : Nat) : Nat := 0

def H68_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H68_a (H68_c x' y) (H68_b x' (H68_c x' y) y)

def H68_aux (x y : Nat) : Nat :=
  if 2 * x > y + 1 then 1 else if 2 * x = y + 1 then 0 else y + 1 - 2 * x

lemma H68_a_val (x y : Nat) : evalPRF H68_a_prf (mk_args2 x y) = H68_a x y := by
  match x with | 0 => rfl | 1 => rfl | x' + 2 => rfl

lemma H68_b_val (x _acc y : Nat) : evalPRF H68_b_prf (mk_args3 x _acc y) = H68_b x _acc y := by
  rfl

lemma H68_c_val (x y : Nat) : evalPRF H68_c_prf (mk_args2 x y) = H68_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp H68_a_prf prf_list![(PRF.proj 3 ⟨1, by decide⟩), H68_b_prf]) (mk_args3 x (evalPRF H68_c_prf (mk_args2 x y)) y) = H68_c (x + 1) y
    rw [ih]
    change evalPRF H68_a_prf (mk_args2 (H68_c x y) (evalPRF H68_b_prf (mk_args3 x (H68_c x y) y))) = H68_a (H68_c x y) (H68_b x (H68_c x y) y)
    rw [H68_b_val, H68_a_val]

lemma H68_comp (x : Nat) : evalPRF holdout_68 (fun _ => x) = evalPRF H68_c_prf (mk_args2 (x+1) 0) := by
  change evalPRF H68_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.zero 1] j (fun _ => x)) = evalPRF H68_c_prf (mk_args2 (x+1) 0)
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

lemma H68_c_cf (x0 y0 : Nat) : H68_c x0 y0 = H68_aux x0 y0 := by
  induction x0 with
  | zero =>
    unfold H68_c H68_aux
    repeat (first | split | rfl | omega)
  | succ x' ih =>
    unfold H68_c H68_b H68_aux
    rw [ih]
    unfold H68_aux
    repeat (
      first
      | split
      | rfl
      | omega
      | have h : y0 + 1 - 2 * x' = 1 := by omega
        rw [h]
        rfl
      | have h : y0 + 1 - 2 * x' = 2 := by omega
        rw [h]
        rfl
      | have h : ∃ k, y0 + 1 - 2 * x' = k + 2 := ⟨y0 + 1 - 2 * x' - 2, by omega⟩
        rcases h with ⟨k, hk⟩
        rw [hk]
        dsimp [H68_a]
        omega
    )

theorem holdout_68_diverges : ∀ x, evalPRF holdout_68 (fun _ => x) > 0 := by
  intro x
  rw [H68_comp x]
  rw [H68_c_val]
  rw [H68_c_cf]
  unfold H68_aux
  have h : 2 * (x + 1) > 0 + 1 := by omega
  simp only [if_pos h]
  omega

-- Translating holdout_69
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,P(1,1)))
def HOLDOUT_69_p1 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def HOLDOUT_69_p2 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_69_p1
def HOLDOUT_69_p3 : PRF 3 := PRF.comp HOLDOUT_69_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.zero 3)]
def HOLDOUT_69_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_69_p3
def HOLDOUT_69_p5 : PRF 1 := PRF.comp HOLDOUT_69_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_69 : PRF 1 := HOLDOUT_69_p5

theorem holdout_69_diverges : ∀ x, evalPRF holdout_69 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_70
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),P(1,1)))
def HOLDOUT_70_p1 : PRF 1 := PRF.primRec (PRF.zero 0) (PRF.proj 2 ⟨0, by decide⟩)
def HOLDOUT_70_p2 : PRF 2 := PRF.primRec HOLDOUT_70_p1 (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_70_p3 : PRF 3 := PRF.comp HOLDOUT_70_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]
def HOLDOUT_70_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_70_p3
def HOLDOUT_70_p5 : PRF 1 := PRF.comp HOLDOUT_70_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_70 : PRF 1 := HOLDOUT_70_p5

theorem holdout_70_diverges : ∀ x, evalPRF holdout_70 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_71
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),S))
def HOLDOUT_71_p1 : PRF 1 := PRF.primRec (PRF.zero 0) (PRF.proj 2 ⟨0, by decide⟩)
def HOLDOUT_71_p2 : PRF 2 := PRF.primRec HOLDOUT_71_p1 (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_71_p3 : PRF 3 := PRF.comp HOLDOUT_71_p2 prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]
def HOLDOUT_71_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_71_p3
def HOLDOUT_71_p5 : PRF 1 := PRF.comp HOLDOUT_71_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_71 : PRF 1 := HOLDOUT_71_p5

theorem holdout_71_diverges : ∀ x, evalPRF holdout_71 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 72
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),S,S))
def holdout_72 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, PRF.succ]

def H72_a_prf : PRF 1 := (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)))
def H72_b_prf : PRF 3 := (PRF.proj 3 ⟨0, by decide⟩)
def H72_c_prf : PRF 2 := (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec H72_a_prf H72_b_prf) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

def H72_a (acc x : Nat) : Nat :=
  match acc with
  | 0 => x - 1
  | acc' + 1 => acc'

def H72_b (acc' _acc x : Nat) : Nat := acc'

def H72_c (x y : Nat) : Nat :=
  match x with
  | 0 => y + 1
  | x' + 1 => H72_a (H72_c x' y) x'

lemma H72_a_val (x : Nat) : evalPRF H72_a_prf (fun _ => x) = H72_a 0 x := by
  change evalPRF (PRF.primRec (PRF.zero 0) (PRF.proj 2 ⟨0, by decide⟩)) (fun _ => x) = x - 1
  induction x with
  | zero => rfl
  | succ x' ih => rfl

lemma H72_b_val (acc' _acc x : Nat) : evalPRF H72_b_prf (mk_args3 acc' _acc x) = H72_b acc' _acc x := by
  rfl

lemma H72_inner (acc x : Nat) : evalPRF (PRF.primRec H72_a_prf H72_b_prf) (mk_args2 acc x) = H72_a acc x := by
  induction acc with
  | zero =>
    change evalPRF H72_a_prf (fun _ => x) = H72_a 0 x
    exact H72_a_val x
  | succ acc' ih =>
    change evalPRF H72_b_prf (mk_args3 acc' (evalPRF (PRF.primRec H72_a_prf H72_b_prf) (mk_args2 acc' x)) x) = H72_a (acc' + 1) x
    rw [ih]
    rfl

lemma H72_c_val (x y : Nat) : evalPRF H72_c_prf (mk_args2 x y) = H72_c x y := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evalPRF (PRF.comp (PRF.primRec H72_a_prf H72_b_prf) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]) (mk_args3 x (evalPRF H72_c_prf (mk_args2 x y)) y) = H72_c (x + 1) y
    rw [ih]
    change evalPRF (PRF.primRec H72_a_prf H72_b_prf) (mk_args2 (H72_c x y) x) = H72_a (H72_c x y) x
    rw [H72_inner]

lemma H72_comp (x : Nat) : evalPRF holdout_72 (fun _ => x) = evalPRF H72_c_prf (mk_args2 (x+1) (x+1)) := by
  change evalPRF H72_c_prf (fun j => evalPRFList prf_list![PRF.succ, PRF.succ] j (fun _ => x)) = evalPRF H72_c_prf (mk_args2 (x+1) (x+1))
  apply congrArg
  funext ⟨val, isLt⟩
  match val with
  | 0 => rfl
  | 1 => rfl

lemma H72_c_cf (x0 y0 : Nat) (h : x0 ≤ y0 + 1) : H72_c x0 y0 = y0 + 1 - x0 := by
  induction x0 with
  | zero =>
    dsimp [H72_c]
  | succ x' ih =>
    have h1 : x' ≤ y0 + 1 := by omega
    have ih_val := ih h1
    dsimp [H72_c, H72_b]
    rw [ih_val]
    have h2 : y0 + 1 - x' > 0 := by omega
    have h3 : ∃ k, y0 + 1 - x' = k + 1 := ⟨y0 + 1 - x' - 1, by omega⟩
    rcases h3 with ⟨k, hk⟩
    rw [hk]
    dsimp [H72_a]
    omega

theorem holdout_72_diverges : ∀ x, evalPRF holdout_72 (fun _ => x) > 0 := by
  intro x
  rw [H72_comp x]
  rw [H72_c_val]
  rw [H72_c_cf (x + 1) (x + 1) (by omega)]
  omega

-- Translating holdout_73
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def HOLDOUT_73_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_73_p2 : PRF 4 := PRF.comp HOLDOUT_73_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_73_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_73_p2
def HOLDOUT_73_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_73_p3
def HOLDOUT_73_p5 : PRF 1 := PRF.comp HOLDOUT_73_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_73 : PRF 1 := HOLDOUT_73_p5

theorem holdout_73_diverges : ∀ x, evalPRF holdout_73 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_74
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_74_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_74_p2 : PRF 4 := PRF.comp HOLDOUT_74_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_74_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_74_p2
def HOLDOUT_74_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_74_p3
def HOLDOUT_74_p5 : PRF 1 := PRF.comp HOLDOUT_74_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_74 : PRF 1 := HOLDOUT_74_p5

theorem holdout_74_diverges : ∀ x, evalPRF holdout_74 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_75
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,P(1,1)))
def HOLDOUT_75_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_75_p2 : PRF 4 := PRF.comp HOLDOUT_75_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_75_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_75_p2
def HOLDOUT_75_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_75_p3
def HOLDOUT_75_p5 : PRF 1 := PRF.comp HOLDOUT_75_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_75 : PRF 1 := HOLDOUT_75_p5

theorem holdout_75_diverges : ∀ x, evalPRF holdout_75 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_76
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_76_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_76_p2 : PRF 4 := PRF.comp HOLDOUT_76_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_76_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_76_p2
def HOLDOUT_76_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_76_p3
def HOLDOUT_76_p5 : PRF 1 := PRF.comp HOLDOUT_76_p4 prf_list![PRF.succ, PRF.succ]
def holdout_76 : PRF 1 := HOLDOUT_76_p5

theorem holdout_76_diverges : ∀ x, evalPRF holdout_76 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_77
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def HOLDOUT_77_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_77_p2 : PRF 4 := PRF.comp HOLDOUT_77_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_77_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_77_p2
def HOLDOUT_77_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_77_p3
def HOLDOUT_77_p5 : PRF 1 := PRF.comp HOLDOUT_77_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_77 : PRF 1 := HOLDOUT_77_p5

theorem holdout_77_diverges : ∀ x, evalPRF holdout_77 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_78
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_78_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_78_p2 : PRF 4 := PRF.comp HOLDOUT_78_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_78_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_78_p2
def HOLDOUT_78_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_78_p3
def HOLDOUT_78_p5 : PRF 1 := PRF.comp HOLDOUT_78_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_78 : PRF 1 := HOLDOUT_78_p5

theorem holdout_78_diverges : ∀ x, evalPRF holdout_78 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_79
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,P(1,1)))
def HOLDOUT_79_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_79_p2 : PRF 4 := PRF.comp HOLDOUT_79_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_79_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_79_p2
def HOLDOUT_79_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_79_p3
def HOLDOUT_79_p5 : PRF 1 := PRF.comp HOLDOUT_79_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_79 : PRF 1 := HOLDOUT_79_p5

theorem holdout_79_diverges : ∀ x, evalPRF holdout_79 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_80
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_80_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_80_p2 : PRF 4 := PRF.comp HOLDOUT_80_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_80_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_80_p2
def HOLDOUT_80_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_80_p3
def HOLDOUT_80_p5 : PRF 1 := PRF.comp HOLDOUT_80_p4 prf_list![PRF.succ, PRF.succ]
def holdout_80 : PRF 1 := HOLDOUT_80_p5

theorem holdout_80_diverges : ∀ x, evalPRF holdout_80 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_81
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),P(1,1)))
def HOLDOUT_81_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_81_p2 : PRF 4 := PRF.comp HOLDOUT_81_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_81_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_81_p2
def HOLDOUT_81_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_81_p3
def HOLDOUT_81_p5 : PRF 1 := PRF.comp HOLDOUT_81_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_81 : PRF 1 := HOLDOUT_81_p5

theorem holdout_81_diverges : ∀ x, evalPRF holdout_81 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_82
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def HOLDOUT_82_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_82_p2 : PRF 4 := PRF.comp HOLDOUT_82_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_82_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_82_p2
def HOLDOUT_82_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_82_p3
def HOLDOUT_82_p5 : PRF 1 := PRF.comp HOLDOUT_82_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_82 : PRF 1 := HOLDOUT_82_p5

theorem holdout_82_diverges : ∀ x, evalPRF holdout_82 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_83
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,P(1,1)))
def HOLDOUT_83_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_83_p2 : PRF 4 := PRF.comp HOLDOUT_83_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_83_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_83_p2
def HOLDOUT_83_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_83_p3
def HOLDOUT_83_p5 : PRF 1 := PRF.comp HOLDOUT_83_p4 prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_83 : PRF 1 := HOLDOUT_83_p5

theorem holdout_83_diverges : ∀ x, evalPRF holdout_83 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_84
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def HOLDOUT_84_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_84_p2 : PRF 4 := PRF.comp HOLDOUT_84_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_84_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) HOLDOUT_84_p2
def HOLDOUT_84_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_84_p3
def HOLDOUT_84_p5 : PRF 1 := PRF.comp HOLDOUT_84_p4 prf_list![PRF.succ, PRF.succ]
def holdout_84 : PRF 1 := HOLDOUT_84_p5

theorem holdout_84_diverges : ∀ x, evalPRF holdout_84 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_85
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),P(1,1)))
def HOLDOUT_85_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_85_p2 : PRF 4 := PRF.comp HOLDOUT_85_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_85_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_85_p2
def HOLDOUT_85_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_85_p3
def HOLDOUT_85_p5 : PRF 1 := PRF.comp HOLDOUT_85_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_85 : PRF 1 := HOLDOUT_85_p5

theorem holdout_85_diverges : ∀ x, evalPRF holdout_85 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_86
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def HOLDOUT_86_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_86_p2 : PRF 4 := PRF.comp HOLDOUT_86_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_86_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_86_p2
def HOLDOUT_86_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_86_p3
def HOLDOUT_86_p5 : PRF 1 := PRF.comp HOLDOUT_86_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_86 : PRF 1 := HOLDOUT_86_p5

theorem holdout_86_diverges : ∀ x, evalPRF holdout_86 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_87
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def HOLDOUT_87_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_87_p2 : PRF 4 := PRF.comp HOLDOUT_87_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_87_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_87_p2
def HOLDOUT_87_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_87_p3
def HOLDOUT_87_p5 : PRF 1 := PRF.comp HOLDOUT_87_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_87 : PRF 1 := HOLDOUT_87_p5

theorem holdout_87_diverges : ∀ x, evalPRF holdout_87 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_88
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_88_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_88_p2 : PRF 4 := PRF.comp HOLDOUT_88_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_88_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_88_p2
def HOLDOUT_88_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_88_p3
def HOLDOUT_88_p5 : PRF 1 := PRF.comp HOLDOUT_88_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_88 : PRF 1 := HOLDOUT_88_p5

theorem holdout_88_diverges : ∀ x, evalPRF holdout_88 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_89
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_89_p1 : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_89_p2 : PRF 4 := PRF.comp HOLDOUT_89_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_89_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_89_p2
def HOLDOUT_89_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_89_p3
def HOLDOUT_89_p5 : PRF 1 := PRF.comp HOLDOUT_89_p4 prf_list![PRF.succ, PRF.succ]
def holdout_89 : PRF 1 := HOLDOUT_89_p5

theorem holdout_89_diverges : ∀ x, evalPRF holdout_89 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_90
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),P(1,1)))
def HOLDOUT_90_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_90_p2 : PRF 4 := PRF.comp HOLDOUT_90_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_90_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_90_p2
def HOLDOUT_90_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_90_p3
def HOLDOUT_90_p5 : PRF 1 := PRF.comp HOLDOUT_90_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_90 : PRF 1 := HOLDOUT_90_p5

theorem holdout_90_diverges : ∀ x, evalPRF holdout_90 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_91
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def HOLDOUT_91_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_91_p2 : PRF 4 := PRF.comp HOLDOUT_91_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_91_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_91_p2
def HOLDOUT_91_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_91_p3
def HOLDOUT_91_p5 : PRF 1 := PRF.comp HOLDOUT_91_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_91 : PRF 1 := HOLDOUT_91_p5

theorem holdout_91_diverges : ∀ x, evalPRF holdout_91 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_92
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),P(1,1)))
def HOLDOUT_92_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_92_p2 : PRF 4 := PRF.comp HOLDOUT_92_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]
def HOLDOUT_92_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_92_p2
def HOLDOUT_92_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_92_p3
def HOLDOUT_92_p5 : PRF 1 := PRF.comp HOLDOUT_92_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_92 : PRF 1 := HOLDOUT_92_p5

theorem holdout_92_diverges : ∀ x, evalPRF holdout_92 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_93
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),S))
def HOLDOUT_93_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_93_p2 : PRF 4 := PRF.comp HOLDOUT_93_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]
def HOLDOUT_93_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_93_p2
def HOLDOUT_93_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_93_p3
def HOLDOUT_93_p5 : PRF 1 := PRF.comp HOLDOUT_93_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_93 : PRF 1 := HOLDOUT_93_p5

theorem holdout_93_diverges : ∀ x, evalPRF holdout_93 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_94
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def HOLDOUT_94_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_94_p2 : PRF 4 := PRF.comp HOLDOUT_94_p1 prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]
def HOLDOUT_94_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_94_p2
def HOLDOUT_94_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_94_p3
def HOLDOUT_94_p5 : PRF 1 := PRF.comp HOLDOUT_94_p4 prf_list![PRF.succ, PRF.succ]
def holdout_94 : PRF 1 := HOLDOUT_94_p5

theorem holdout_94_diverges : ∀ x, evalPRF holdout_94 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_95
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def HOLDOUT_95_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_95_p2 : PRF 4 := PRF.comp HOLDOUT_95_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_95_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_95_p2
def HOLDOUT_95_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_95_p3
def HOLDOUT_95_p5 : PRF 1 := PRF.comp HOLDOUT_95_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_95 : PRF 1 := HOLDOUT_95_p5

theorem holdout_95_diverges : ∀ x, evalPRF holdout_95 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_96
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def HOLDOUT_96_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_96_p2 : PRF 4 := PRF.comp HOLDOUT_96_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_96_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_96_p2
def HOLDOUT_96_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_96_p3
def HOLDOUT_96_p5 : PRF 1 := PRF.comp HOLDOUT_96_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_96 : PRF 1 := HOLDOUT_96_p5

theorem holdout_96_diverges : ∀ x, evalPRF holdout_96 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_97
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def HOLDOUT_97_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_97_p2 : PRF 4 := PRF.comp HOLDOUT_97_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]
def HOLDOUT_97_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_97_p2
def HOLDOUT_97_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_97_p3
def HOLDOUT_97_p5 : PRF 1 := PRF.comp HOLDOUT_97_p4 prf_list![PRF.succ, PRF.succ]
def holdout_97 : PRF 1 := HOLDOUT_97_p5

theorem holdout_97_diverges : ∀ x, evalPRF holdout_97 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_98
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),P(1,1)))
def HOLDOUT_98_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_98_p2 : PRF 4 := PRF.comp HOLDOUT_98_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_98_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_98_p2
def HOLDOUT_98_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_98_p3
def HOLDOUT_98_p5 : PRF 1 := PRF.comp HOLDOUT_98_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]
def holdout_98 : PRF 1 := HOLDOUT_98_p5

theorem holdout_98_diverges : ∀ x, evalPRF holdout_98 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_99
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def HOLDOUT_99_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_99_p2 : PRF 4 := PRF.comp HOLDOUT_99_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_99_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_99_p2
def HOLDOUT_99_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_99_p3
def HOLDOUT_99_p5 : PRF 1 := PRF.comp HOLDOUT_99_p4 prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]
def holdout_99 : PRF 1 := HOLDOUT_99_p5

theorem holdout_99_diverges : ∀ x, evalPRF holdout_99 (fun _ => x) > 0 := by
  sorry

-- Translating holdout_100
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def HOLDOUT_100_p1 : PRF 2 := PRF.primRec PRF.succ (PRF.proj 3 ⟨0, by decide⟩)
def HOLDOUT_100_p2 : PRF 4 := PRF.comp HOLDOUT_100_p1 prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]
def HOLDOUT_100_p3 : PRF 3 := PRF.primRec (PRF.proj 2 ⟨1, by decide⟩) HOLDOUT_100_p2
def HOLDOUT_100_p4 : PRF 2 := PRF.primRec PRF.succ HOLDOUT_100_p3
def HOLDOUT_100_p5 : PRF 1 := PRF.comp HOLDOUT_100_p4 prf_list![PRF.succ, PRF.succ]
def holdout_100 : PRF 1 := HOLDOUT_100_p5

theorem holdout_100_diverges : ∀ x, evalPRF holdout_100 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 101
-- M(R(C(S,Z0),R(P(1,1),C(R(Z0,R(S,P(3,1))),P(3,2)))))
def holdout_101 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)]))

def H101_b_prf : PRF 3 := (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)])
def H101_h_prf : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H101_b_prf

lemma H101_b_eval (x : Nat) : evalPRF H101_b_prf (mk_args3 x 1 1) = 1 := by
  rfl

lemma H101_h_eval (x : Nat) : evalPRF H101_h_prf (mk_args2 x 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H101_b_prf (mk_args3 x' (evalPRF H101_h_prf (mk_args2 x' 1)) 1) = 1
    rw [ih]
    exact H101_b_eval x'

lemma H101_eval (x : Nat) : evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H101_h_prf) (fun _ => x) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H101_h_prf (mk_args2 x' (evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H101_h_prf) (fun _ => x'))) = 1
    rw [ih]
    exact H101_h_eval x'

theorem holdout_101_diverges : ∀ x, evalPRF holdout_101 (fun _ => x) > 0 := by
  intro x
  change evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H101_h_prf) (fun _ => x) > 0
  rw [H101_eval x]
  decide


-- Translating holdout 102
-- M(R(C(S,Z0),R(P(1,1),R(R(Z1,R(P(2,2),P(4,1))),P(4,2)))))
def holdout_102 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

def H102_b_prf : PRF 3 := (PRF.primRec (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))
def H102_h_prf : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H102_b_prf

lemma H102_b_eval (x : Nat) : evalPRF H102_b_prf (mk_args3 x 1 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H102_b_prf (mk_args3 x' 1 1) = 1
    rw [ih]

lemma H102_h_eval (x : Nat) : evalPRF H102_h_prf (mk_args2 x 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H102_b_prf (mk_args3 x' (evalPRF H102_h_prf (mk_args2 x' 1)) 1) = 1
    rw [ih]
    exact H102_b_eval x'

lemma H102_eval (x : Nat) : evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H102_h_prf) (fun _ => x) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H102_h_prf (mk_args2 x' (evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H102_h_prf) (fun _ => x'))) = 1
    rw [ih]
    exact H102_h_eval x'

theorem holdout_102_diverges : ∀ x, evalPRF holdout_102 (fun _ => x) > 0 := by
  intro x
  change evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H102_h_prf) (fun _ => x) > 0
  rw [H102_eval x]
  decide


-- Translating holdout 103
-- M(R(C(S,Z0),R(P(1,1),R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2)))))
def holdout_103 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

def H103_b_prf : PRF 3 := (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))
def H103_h_prf : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H103_b_prf

lemma H103_b_eval (x : Nat) : evalPRF H103_b_prf (mk_args3 x 1 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H103_b_prf (mk_args3 x' 1 1) = 1
    rw [ih]

lemma H103_h_eval (x : Nat) : evalPRF H103_h_prf (mk_args2 x 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H103_b_prf (mk_args3 x' (evalPRF H103_h_prf (mk_args2 x' 1)) 1) = 1
    rw [ih]
    exact H103_b_eval x'

lemma H103_eval (x : Nat) : evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H103_h_prf) (fun _ => x) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H103_h_prf (mk_args2 x' (evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H103_h_prf) (fun _ => x'))) = 1
    rw [ih]
    exact H103_h_eval x'

theorem holdout_103_diverges : ∀ x, evalPRF holdout_103 (fun _ => x) > 0 := by
  intro x
  change evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H103_h_prf) (fun _ => x) > 0
  rw [H103_eval x]
  decide


-- Translating holdout 104
-- M(R(C(S,Z0),R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2)))))
def H104_h4_prf : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def H104_g3_prf : PRF 2 := PRF.primRec (PRF.succ) H104_h4_prf
def H104_h2_prf : PRF 3 := PRF.primRec H104_g3_prf (PRF.proj 4 ⟨1, by decide⟩)
def H104_h_prf : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) H104_h2_prf
def H104_g_prf : PRF 0 := PRF.comp PRF.succ prf_list![PRF.zero 0]

def holdout_104 : PRF 1 := PRF.primRec H104_g_prf H104_h_prf

lemma holdout_104_eq : holdout_104 = PRF.primRec H104_g_prf H104_h_prf := rfl

def H104_h4_val (m4 acc4 : Nat) : Nat :=
  match m4 with
  | 0 => acc4
  | m' + 1 => m'

lemma H104_h4_eval (m4 acc4 acc : Nat) :
  evalPRF H104_h4_prf (mk_args3 m4 acc4 acc) = H104_h4_val m4 acc4 := by
  cases m4 <;> rfl

def H104_g3_val (acc2 acc : Nat) : Nat :=
  match acc2 with
  | 0 => acc + 1
  | 1 => acc + 1
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | x + 2 => x

lemma H104_g3_eval (acc2 acc : Nat) :
  evalPRF H104_g3_prf (mk_args2 acc2 acc) = H104_g3_val acc2 acc := by
  induction acc2 with
  | zero => rfl
  | succ a ih =>
    have h_step : evalPRF (PRF.primRec (PRF.succ) H104_h4_prf) (mk_args2 (a + 1) acc) = evalPRF H104_h4_prf (mk_args3 a (evalPRF (PRF.primRec (PRF.succ) H104_h4_prf) (mk_args2 a acc)) acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H104_g3_prf
    rw [h_step]
    change evalPRF H104_h4_prf (mk_args3 a (evalPRF H104_g3_prf (mk_args2 a acc)) acc) = H104_g3_val (a + 1) acc
    rw [ih]
    rw [H104_h4_eval]
    cases a with
    | zero => rfl
    | succ a' => cases a' with
      | zero => rfl
      | succ a'' => cases a'' with
        | zero => rfl
        | succ a''' => cases a''' with
          | zero => rfl
          | succ _ => rfl

def H104_h2_val (acc2 acc : Nat) : Nat := H104_g3_val acc2 acc

lemma H104_h2_eval (m2 acc2 acc : Nat) :
  evalPRF H104_h2_prf (mk_args3 m2 acc2 acc) = H104_h2_val acc2 acc := by
  induction m2 with
  | zero =>
    have h_step : evalPRF (PRF.primRec H104_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 0 acc2 acc) = evalPRF H104_g3_prf (mk_args2 acc2 acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H104_h2_prf
    rw [h_step]
    exact H104_g3_eval acc2 acc
  | succ m' ih =>
    have h_step : evalPRF (PRF.primRec H104_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 (m' + 1) acc2 acc) = evalPRF (PRF.proj 4 ⟨1, by decide⟩) (mk_args4 m' (evalPRF (PRF.primRec H104_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 m' acc2 acc)) acc2 acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H104_h2_prf
    rw [h_step]
    change evalPRF H104_h2_prf (mk_args3 m' acc2 acc) = H104_h2_val acc2 acc
    rw [ih]

def H104_h_val (m acc : Nat) : Nat :=
  match m with
  | 0 => acc
  | m' + 1 => H104_h2_val (H104_h_val m' acc) acc

lemma H104_h_eval (m acc : Nat) :
  evalPRF H104_h_prf (mk_args2 m acc) = H104_h_val m acc := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    have h_step : evalPRF (PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) H104_h2_prf) (mk_args2 (m' + 1) acc) = evalPRF H104_h2_prf (mk_args3 m' (evalPRF (PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) H104_h2_prf) (mk_args2 m' acc)) acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H104_h_prf
    rw [h_step]
    change evalPRF H104_h2_prf (mk_args3 m' (evalPRF H104_h_prf (mk_args2 m' acc)) acc) = H104_h_val (m' + 1) acc
    rw [ih]
    exact H104_h2_eval m' (H104_h_val m' acc) acc

def holdout_104_val (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x' + 1 => H104_h_val x' (holdout_104_val x')

lemma holdout_104_eval (x : Nat) :
  evalPRF holdout_104 (fun _ => x) = holdout_104_val x := by
  rw [holdout_104_eq]
  induction x with
  | zero => rfl
  | succ x' ih =>
    have h_step : evalPRF (PRF.primRec H104_g_prf H104_h_prf) (fun _ => x' + 1) = evalPRF H104_h_prf (mk_args2 x' (evalPRF (PRF.primRec H104_g_prf H104_h_prf) (fun _ => x'))) := by
      unfold evalPRF
      dsimp
      congr
    rw [h_step]
    change evalPRF H104_h_prf (mk_args2 x' (evalPRF (PRF.primRec H104_g_prf H104_h_prf) (fun _ => x'))) = holdout_104_val (x' + 1)
    rw [ih]
    exact H104_h_eval x' (holdout_104_val x')

lemma holdout_104_val_pos (x : Nat) : holdout_104_val x > 0 := by
  cases x with
  | zero => decide
  | succ x' => cases x' with
    | zero => decide
    | succ x'' =>
      have h_osc : ∀ k, holdout_104_val (k + 2) = 2 ∨ holdout_104_val (k + 2) = 3 := by
        intro k
        induction k with
        | zero => left; rfl
        | succ k' ih =>
          cases ih with
          | inl h2 =>
            right
            change H104_h_val (k' + 2) (holdout_104_val (k' + 2)) = 3
            rw [h2]
            -- At this point we'd need to evaluate H104_h_val m 2, which requires induction on m
            sorry
          | inr h3 =>
            left
            change H104_h_val (k' + 2) (holdout_104_val (k' + 2)) = 2
            rw [h3]
            sorry
      have h_pos : holdout_104_val (x'' + 2) = 2 ∨ holdout_104_val (x'' + 2) = 3 := h_osc x''
      cases h_pos with
      | inl h2 => rw [h2]; decide
      | inr h3 => rw [h3]; decide

theorem holdout_104_diverges : ∀ x, evalPRF holdout_104 (fun _ => x) > 0 := by
  intro x
  rw [holdout_104_eval x]
  exact holdout_104_val_pos x

-- Translating holdout 105
-- M(R(C(S,Z0),R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2)))))
def holdout_105 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

def H105_b_prf : PRF 3 := (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))
def H105_h_prf : PRF 2 := PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) H105_b_prf

lemma H105_b_eval (x : Nat) : evalPRF H105_b_prf (mk_args3 x 1 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H105_b_prf (mk_args3 x' 1 1) = 1
    rw [ih]

lemma H105_h_eval (x : Nat) : evalPRF H105_h_prf (mk_args2 x 1) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H105_b_prf (mk_args3 x' (evalPRF H105_h_prf (mk_args2 x' 1)) 1) = 1
    rw [ih]
    exact H105_b_eval x'

lemma H105_eval (x : Nat) : evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H105_h_prf) (fun _ => x) = 1 := by
  induction x with
  | zero => rfl
  | succ x' ih =>
    change evalPRF H105_h_prf (mk_args2 x' (evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H105_h_prf) (fun _ => x'))) = 1
    rw [ih]
    exact H105_h_eval x'

theorem holdout_105_diverges : ∀ x, evalPRF holdout_105 (fun _ => x) > 0 := by
  intro x
  change evalPRF (PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) H105_h_prf) (fun _ => x) > 0
  rw [H105_eval x]
  decide


-- Translating holdout 106
-- M(R(C(S,Z0),R(S,R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2)))))
def H106_h4_prf : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def H106_g3_prf : PRF 2 := PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) H106_h4_prf
def H106_h2_prf : PRF 3 := PRF.primRec H106_g3_prf (PRF.proj 4 ⟨1, by decide⟩)
def H106_h_prf : PRF 2 := PRF.primRec (PRF.succ) H106_h2_prf
def H106_g_prf : PRF 0 := PRF.comp PRF.succ prf_list![PRF.zero 0]

def holdout_106 : PRF 1 := PRF.primRec H106_g_prf H106_h_prf

lemma holdout_106_eq : holdout_106 = PRF.primRec H106_g_prf H106_h_prf := rfl

def H106_h4_val (m4 acc4 : Nat) : Nat :=
  match m4 with
  | 0 => acc4
  | m' + 1 => m'

lemma H106_h4_eval (m4 acc4 acc : Nat) :
  evalPRF H106_h4_prf (mk_args3 m4 acc4 acc) = H106_h4_val m4 acc4 := by
  cases m4 <;> rfl

def H106_g3_val (acc2 acc : Nat) : Nat :=
  match acc2 with
  | 0 => acc
  | 1 => acc
  | m' + 2 => m'

lemma H106_g3_eval (acc2 acc : Nat) :
  evalPRF H106_g3_prf (mk_args2 acc2 acc) = H106_g3_val acc2 acc := by
  induction acc2 with
  | zero => rfl
  | succ a ih =>
    have h_step : evalPRF (PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) H106_h4_prf) (mk_args2 (a + 1) acc) = evalPRF H106_h4_prf (mk_args3 a (evalPRF (PRF.primRec (PRF.proj 1 ⟨0, by decide⟩) H106_h4_prf) (mk_args2 a acc)) acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H106_g3_prf
    rw [h_step]
    change evalPRF H106_h4_prf (mk_args3 a (evalPRF H106_g3_prf (mk_args2 a acc)) acc) = H106_g3_val (a + 1) acc
    rw [ih]
    rw [H106_h4_eval]
    cases a with
    | zero => rfl
    | succ a' => cases a' with
      | zero => rfl
      | succ _ => rfl

def H106_h2_val (acc2 acc : Nat) : Nat := H106_g3_val acc2 acc

lemma H106_h2_eval (m2 acc2 acc : Nat) :
  evalPRF H106_h2_prf (mk_args3 m2 acc2 acc) = H106_h2_val acc2 acc := by
  induction m2 with
  | zero =>
    have h_step : evalPRF (PRF.primRec H106_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 0 acc2 acc) = evalPRF H106_g3_prf (mk_args2 acc2 acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H106_h2_prf
    rw [h_step]
    exact H106_g3_eval acc2 acc
  | succ m' ih =>
    have h_step : evalPRF (PRF.primRec H106_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 (m' + 1) acc2 acc) = evalPRF (PRF.proj 4 ⟨1, by decide⟩) (mk_args4 m' (evalPRF (PRF.primRec H106_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 m' acc2 acc)) acc2 acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H106_h2_prf
    rw [h_step]
    change evalPRF H106_h2_prf (mk_args3 m' acc2 acc) = H106_h2_val acc2 acc
    rw [ih]

def H106_h_val (m acc : Nat) : Nat :=
  match m with
  | 0 => acc + 1
  | m' + 1 => H106_h2_val (H106_h_val m' acc) acc

lemma H106_h_eval (m acc : Nat) :
  evalPRF H106_h_prf (mk_args2 m acc) = H106_h_val m acc := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    have h_step : evalPRF (PRF.primRec (PRF.succ) H106_h2_prf) (mk_args2 (m' + 1) acc) = evalPRF H106_h2_prf (mk_args3 m' (evalPRF (PRF.primRec (PRF.succ) H106_h2_prf) (mk_args2 m' acc)) acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H106_h_prf
    rw [h_step]
    change evalPRF H106_h2_prf (mk_args3 m' (evalPRF H106_h_prf (mk_args2 m' acc)) acc) = H106_h_val (m' + 1) acc
    rw [ih]
    exact H106_h2_eval m' (H106_h_val m' acc) acc

def holdout_106_val (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x' + 1 => H106_h_val x' (holdout_106_val x')

lemma holdout_106_eval (x : Nat) :
  evalPRF holdout_106 (fun _ => x) = holdout_106_val x := by
  rw [holdout_106_eq]
  induction x with
  | zero => rfl
  | succ x' ih =>
    have h_step : evalPRF (PRF.primRec H106_g_prf H106_h_prf) (fun _ => x' + 1) = evalPRF H106_h_prf (mk_args2 x' (evalPRF (PRF.primRec H106_g_prf H106_h_prf) (fun _ => x'))) := by
      unfold evalPRF
      dsimp
      congr
    rw [h_step]
    change evalPRF H106_h_prf (mk_args2 x' (evalPRF (PRF.primRec H106_g_prf H106_h_prf) (fun _ => x'))) = holdout_106_val (x' + 1)
    rw [ih]
    exact H106_h_eval x' (holdout_106_val x')

lemma holdout_106_val_pos (x : Nat) : holdout_106_val x > 0 := by
  sorry

theorem holdout_106_diverges : ∀ x, evalPRF holdout_106 (fun _ => x) > 0 := by
  intro x
  rw [holdout_106_eval x]
  exact holdout_106_val_pos x

-- Translating holdout 107
-- M(R(C(S,Z0),R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2)))))
def H107_h4_prf : PRF 3 := PRF.primRec (PRF.proj 2 ⟨0, by decide⟩) (PRF.proj 4 ⟨0, by decide⟩)
def H107_g3_prf : PRF 2 := PRF.primRec (PRF.succ) H107_h4_prf
def H107_h2_prf : PRF 3 := PRF.primRec H107_g3_prf (PRF.proj 4 ⟨1, by decide⟩)
def H107_h_prf : PRF 2 := PRF.primRec (PRF.succ) H107_h2_prf
def H107_g_prf : PRF 0 := PRF.comp PRF.succ prf_list![PRF.zero 0]

def holdout_107 : PRF 1 := PRF.primRec H107_g_prf H107_h_prf

lemma holdout_107_eq : holdout_107 = PRF.primRec H107_g_prf H107_h_prf := rfl

def H107_h4_val (m4 acc4 : Nat) : Nat :=
  match m4 with
  | 0 => acc4
  | m' + 1 => m'

lemma H107_h4_eval (m4 acc4 acc : Nat) :
  evalPRF H107_h4_prf (mk_args3 m4 acc4 acc) = H107_h4_val m4 acc4 := by
  cases m4 <;> rfl

def H107_g3_val (acc2 acc : Nat) : Nat :=
  match acc2 with
  | 0 => acc + 1
  | 1 => acc + 1
  | m' + 2 => m'

lemma H107_g3_eval (acc2 acc : Nat) :
  evalPRF H107_g3_prf (mk_args2 acc2 acc) = H107_g3_val acc2 acc := by
  induction acc2 with
  | zero => rfl
  | succ a ih =>
    have h_step : evalPRF (PRF.primRec (PRF.succ) H107_h4_prf) (mk_args2 (a + 1) acc) = evalPRF H107_h4_prf (mk_args3 a (evalPRF (PRF.primRec (PRF.succ) H107_h4_prf) (mk_args2 a acc)) acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H107_g3_prf
    rw [h_step]
    change evalPRF H107_h4_prf (mk_args3 a (evalPRF H107_g3_prf (mk_args2 a acc)) acc) = H107_g3_val (a + 1) acc
    rw [ih]
    rw [H107_h4_eval]
    cases a with
    | zero => rfl
    | succ a' => cases a' with
      | zero => rfl
      | succ _ => rfl

def H107_h2_val (acc2 acc : Nat) : Nat := H107_g3_val acc2 acc

lemma H107_h2_eval (m2 acc2 acc : Nat) :
  evalPRF H107_h2_prf (mk_args3 m2 acc2 acc) = H107_h2_val acc2 acc := by
  induction m2 with
  | zero =>
    have h_step : evalPRF (PRF.primRec H107_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 0 acc2 acc) = evalPRF H107_g3_prf (mk_args2 acc2 acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H107_h2_prf
    rw [h_step]
    exact H107_g3_eval acc2 acc
  | succ m' ih =>
    have h_step : evalPRF (PRF.primRec H107_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 (m' + 1) acc2 acc) = evalPRF (PRF.proj 4 ⟨1, by decide⟩) (mk_args4 m' (evalPRF (PRF.primRec H107_g3_prf (PRF.proj 4 ⟨1, by decide⟩)) (mk_args3 m' acc2 acc)) acc2 acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H107_h2_prf
    rw [h_step]
    change evalPRF H107_h2_prf (mk_args3 m' acc2 acc) = H107_h2_val acc2 acc
    rw [ih]

def H107_h_val (m acc : Nat) : Nat :=
  match m with
  | 0 => acc + 1
  | m' + 1 => H107_h2_val (H107_h_val m' acc) acc

lemma H107_h_eval (m acc : Nat) :
  evalPRF H107_h_prf (mk_args2 m acc) = H107_h_val m acc := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    have h_step : evalPRF (PRF.primRec (PRF.succ) H107_h2_prf) (mk_args2 (m' + 1) acc) = evalPRF H107_h2_prf (mk_args3 m' (evalPRF (PRF.primRec (PRF.succ) H107_h2_prf) (mk_args2 m' acc)) acc) := by
      unfold evalPRF
      dsimp
      congr
    unfold H107_h_prf
    rw [h_step]
    change evalPRF H107_h2_prf (mk_args3 m' (evalPRF H107_h_prf (mk_args2 m' acc)) acc) = H107_h_val (m' + 1) acc
    rw [ih]
    exact H107_h2_eval m' (H107_h_val m' acc) acc

def holdout_107_val (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x' + 1 => H107_h_val x' (holdout_107_val x')

lemma holdout_107_eval (x : Nat) :
  evalPRF holdout_107 (fun _ => x) = holdout_107_val x := by
  rw [holdout_107_eq]
  induction x with
  | zero => rfl
  | succ x' ih =>
    have h_step : evalPRF (PRF.primRec H107_g_prf H107_h_prf) (fun _ => x' + 1) = evalPRF H107_h_prf (mk_args2 x' (evalPRF (PRF.primRec H107_g_prf H107_h_prf) (fun _ => x'))) := by
      unfold evalPRF
      dsimp
      congr
    rw [h_step]
    change evalPRF H107_h_prf (mk_args2 x' (evalPRF (PRF.primRec H107_g_prf H107_h_prf) (fun _ => x'))) = holdout_107_val (x' + 1)
    rw [ih]
    exact H107_h_eval x' (holdout_107_val x')

lemma holdout_107_val_pos (x : Nat) : holdout_107_val x > 0 := by
  sorry

theorem holdout_107_diverges : ∀ x, evalPRF holdout_107 (fun _ => x) > 0 := by
  intro x
  rw [holdout_107_eval x]
  exact holdout_107_val_pos x

end Holdouts14
