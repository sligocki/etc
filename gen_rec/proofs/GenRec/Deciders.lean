import GenRec.Semantics

open GenRec

namespace GenRec.Deciders

def ParityLoop2 (init y z k : Nat) : Nat :=
  match k with
  | 0 => init
  | k' + 1 => 
    let a := ParityLoop2 init y z k'
    if a = 0 then y else if a = 1 then z else a - 2

lemma ParityLoop2_dec (init y z k : Nat) (h_init : init = y) (hle : 2 * k ≤ y) : ParityLoop2 init y z k = y - 2 * k := by
  induction k with
  | zero => 
    unfold ParityLoop2
    omega
  | succ k' ih =>
    have hle' : 2 * k' ≤ y := by omega
    have ih' := ih hle'
    unfold ParityLoop2
    rw [ih']
    dsimp
    split
    · omega
    · split
      · omega
      · omega

lemma ParityLoop2_even_y (init y z m : Nat) (h_init : init = y) (hm : y = 2 * m) (j : Nat) (hle : 2 * j ≤ y) :
  ParityLoop2 init y z (m + 1 + j) = y - 2 * j := by
  induction j with
  | zero =>
    have h1 : ParityLoop2 init y z m = 0 := by
      have hle_m : 2 * m ≤ y := by omega
      have h_dec := ParityLoop2_dec init y z m h_init hle_m
      omega
    have h2 : ParityLoop2 init y z (m + 1) = y := by
      unfold ParityLoop2
      rw [h1]
      rfl
    omega
  | succ j' ih =>
    have hle' : 2 * j' ≤ y := by omega
    have ih' := ih hle'
    have h_next : m + 1 + (j' + 1) = (m + 1 + j') + 1 := by omega
    rw [h_next]
    unfold ParityLoop2
    rw [ih']
    dsimp
    split
    · omega
    · split
      · omega
      · omega

lemma ParityLoop2_odd_y (init y z m : Nat) (h_init : init = y) (hm : y = 2 * m + 1) (j : Nat) (hle : 2 * j ≤ z) :
  ParityLoop2 init y z (m + 1 + j) = z - 2 * j := by
  induction j with
  | zero =>
    have h1 : ParityLoop2 init y z m = 1 := by
      have hle_m : 2 * m ≤ y := by omega
      have h_dec := ParityLoop2_dec init y z m h_init hle_m
      omega
    have h2 : ParityLoop2 init y z (m + 1) = z := by
      unfold ParityLoop2; rw [h1]; rfl
    omega
  | succ j' ih =>
    have hle' : 2 * j' ≤ z := by omega
    have ih' := ih hle'
    have h_next : m + 1 + (j' + 1) = (m + 1 + j') + 1 := by omega
    rw [h_next]
    unfold ParityLoop2; rw [ih']; dsimp
    split
    · omega
    · split
      · omega
      · omega


-- We can add ParityLoop2_odd_z or other variants here if needed

end GenRec.Deciders
