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


lemma evalPRFList_cons_eq {k m : Nat} (g : PRF k) (gs : PRFList k m) (args : Fin k → Nat) :
  (fun i => evalPRFList (PRFList.cons g gs) i args) =
  (fun i => if h : i.val = 0 then evalPRF g args else evalPRFList gs ⟨i.val - 1, by omega⟩ args) := by
  funext ⟨i, hi⟩
  cases i with
  | zero => simp [evalPRFList]
  | succ i => simp [evalPRFList]

lemma evalPRF_primRec_eq {k : Nat} (g : PRF k) (h : PRF (k + 2)) (args : Fin (k + 1) → Nat) :
  evalPRF (PRF.primRec g h) args =
  let n := args ⟨0, Nat.zero_lt_succ _⟩
  let rest : Fin k → Nat := fun j => args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  let step (m : Nat) (acc : Nat) : Nat :=
    evalPRF h (fun i => if _h1 : i.val = 0 then m else if _h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)
  n.recOn (evalPRF g rest) step := rfl

lemma primRec_computes {k : Nat} (g : PRF k) (h : PRF (k + 2)) (rest : Fin k → Nat) (n : Nat)
  (hg : ComputesTo (Expr.app g (fun j => Expr.val (rest j))) (Expr.val (evalPRF g rest)))
  (hh : ∀ m acc, ComputesTo (Expr.app h (fun i => Expr.val (if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)))
          (Expr.val (evalPRF h (fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)))) :
  ComputesTo (Expr.app (PRF.primRec g h) (fun i => Expr.val (if h_i : i.val = 0 then n else rest ⟨i.val - 1, by omega⟩)))
             (Expr.val (n.recOn (evalPRF g rest) (fun m acc => evalPRF h (fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)))) := by
  induction n with
  | zero =>
    have h_args : (fun i : Fin (k + 1) => Expr.val (if h_i : i.val = 0 then 0 else rest ⟨i.val - 1, by omega⟩)) =
                  (fun i => if h_i : i.val = 0 then Expr.val 0 else Expr.val (rest ⟨i.val - 1, by omega⟩)) := by
      funext i; split <;> rfl
    rw [h_args]
    apply ComputesTo.rec_zero
    · simp
      exact ComputesTo.val_refl _
    · intro j
      simp
      exact ComputesTo.val_refl _
    · exact hg
  | succ n ih =>
    have h_args : (fun i : Fin (k + 1) => Expr.val (if h_i : i.val = 0 then n + 1 else rest ⟨i.val - 1, by omega⟩)) =
                  (fun i => if h_i : i.val = 0 then Expr.val (n + 1) else Expr.val (rest ⟨i.val - 1, by omega⟩)) := by
      funext i; split <;> rfl
    rw [h_args]
    have ih_args : ComputesTo (Expr.app (PRF.primRec g h) (fun i => if h_i : i.val = 0 then Expr.val n else Expr.val (rest ⟨i.val - 1, by omega⟩)))
                 (Expr.val (n.recOn (evalPRF g rest) fun m acc => evalPRF h fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)) := by
      have h_ih_args : (fun i : Fin (k + 1) => if h_i : i.val = 0 then Expr.val n else Expr.val (rest ⟨i.val - 1, by omega⟩)) =
                       (fun i => Expr.val (if h_i : i.val = 0 then n else rest ⟨i.val - 1, by omega⟩)) := by
        funext i; symm; split <;> rfl
      rw [h_ih_args]
      exact ih
    have hh_app := hh n (n.recOn (evalPRF g rest) fun m acc => evalPRF h fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)
    have hh_args : ComputesTo (Expr.app h (fun i => if _h1 : i.val = 0 then Expr.val n else if _h2 : i.val = 1 then Expr.val (n.recOn (evalPRF g rest) fun m acc => evalPRF h fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩) else Expr.val (rest ⟨i.val - 2, by omega⟩)))
                 (Expr.val (evalPRF h fun i => if h1 : i.val = 0 then n else if h2 : i.val = 1 then n.recOn (evalPRF g rest) fun m acc => evalPRF h fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩ else rest ⟨i.val - 2, by omega⟩)) := by
      have h_hh_args : (fun i : Fin (k + 2) => if _h1 : i.val = 0 then Expr.val n else if _h2 : i.val = 1 then Expr.val (n.recOn (evalPRF g rest) fun m acc => evalPRF h fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩) else Expr.val (rest ⟨i.val - 2, by omega⟩)) =
                       (fun i => Expr.val (if h1 : i.val = 0 then n else if h2 : i.val = 1 then n.recOn (evalPRF g rest) fun m acc => evalPRF h fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩ else rest ⟨i.val - 2, by omega⟩)) := by
        funext i
        by_cases h1 : i.val = 0
        · simp [h1]
        · simp [h1]
          by_cases h2 : i.val = 1
          · simp [h2]
          · simp [h2]
      rw [h_hh_args]
      exact hh_app
    apply ComputesTo.rec_succ _ _ _ n rest (n.recOn (evalPRF g rest) (fun m acc => evalPRF h (fun i => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else rest ⟨i.val - 2, by omega⟩)))
    · simp
      exact ComputesTo.val_refl _
    · intro j
      simp
      exact ComputesTo.val_refl _
    · exact ih_args
    · exact hh_args

mutual
/-- Proves that `evalPRF` evaluation implies `ComputesTo` -/
theorem evalPRF_to_ComputesTo : {k : Nat} → (prf : PRF k) → (args : Fin k → Nat) →
  ComputesTo (Expr.app prf (fun i => Expr.val (args i))) (Expr.val (evalPRF prf args))
| _, PRF.zero _, args => ComputesTo.zero _
| _, PRF.succ, args => ComputesTo.succ _ _ (ComputesTo.val_refl _)
| _, PRF.proj _ i, args => ComputesTo.proj _ _ _ (ComputesTo.val_refl _)
| _, PRF.comp h gs, args =>
  ComputesTo.comp h gs (fun i => Expr.val (args i)) (fun i => evalPRFList gs i args) _ (evalPRFList_to_ComputesToList gs args) (evalPRF_to_ComputesTo h _)
| _, @PRF.primRec k g h, args => by
  have hg := evalPRF_to_ComputesTo g (fun (j : Fin k) => args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
  have hh := fun m acc => evalPRF_to_ComputesTo h (fun (i : Fin (k + 2)) => if h1 : i.val = 0 then m else if h2 : i.val = 1 then acc else args ⟨(⟨i.val - 2, by omega⟩ : Fin k).val + 1, Nat.succ_lt_succ (⟨i.val - 2, by omega⟩ : Fin k).isLt⟩)
  have h_ind := primRec_computes g h (fun (j : Fin k) => args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) (args ⟨0, Nat.zero_lt_succ _⟩) hg hh
  have h_eq : (fun (i : Fin (k + 1)) => Expr.val (if h_i : i.val = 0 then args ⟨0, Nat.zero_lt_succ _⟩ else (fun (j : Fin k) => args ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ⟨i.val - 1, by omega⟩)) =
              (fun (i : Fin (k + 1)) => Expr.val (args i)) := by
    funext ⟨i, hi⟩
    cases i
    · simp
    · simp
  rw [h_eq] at h_ind
  rw [evalPRF_primRec_eq]
  exact h_ind

theorem evalPRFList_to_ComputesToList : {k m : Nat} → (gs : PRFList k m) → (args : Fin k → Nat) →
  ComputesToList gs (fun i => Expr.val (args i)) (fun i => evalPRFList gs i args)
| _, _, PRFList.nil, args => ComputesToList.nil _
| _, _, PRFList.cons g gs, args => by
  have h_g := evalPRF_to_ComputesTo g args
  have h_gs := evalPRFList_to_ComputesToList gs args
  have h_eq : (fun i => evalPRFList (PRFList.cons g gs) i args) =
              (fun i => if h : i.val = 0 then evalPRF g args else evalPRFList gs ⟨i.val - 1, by omega⟩ args) :=
    evalPRFList_cons_eq g gs args
  rw [h_eq]
  exact ComputesToList.cons g gs (fun i => Expr.val (args i)) (evalPRF g args) (fun i => evalPRFList gs i args) h_g h_gs
end

end GenRec
