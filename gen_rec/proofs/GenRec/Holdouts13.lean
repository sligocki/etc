import GenRec.Syntax
import GenRec.Semantics

open GenRec

namespace Holdouts13

-- Translating holdout 1
-- M(C(R(Z1,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_1 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_1_diverges : ∀ x, evalPRF holdout_1 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 2
-- M(C(R(P(1,1),R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2))),S,S))
def holdout_2 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

theorem holdout_2_diverges : ∀ x, evalPRF holdout_2 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 3
-- M(C(R(P(1,1),R(R(S,R(Z2,P(4,1))),P(4,2))),S,P(1,1)))
def holdout_3 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_3_diverges : ∀ x, evalPRF holdout_3 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 4
-- M(C(R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_4 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_4_diverges : ∀ x, evalPRF holdout_4 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 5
-- M(C(R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,S))
def holdout_5 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

theorem holdout_5_diverges : ∀ x, evalPRF holdout_5 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 6
-- M(C(R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2))),S,P(1,1)))
def holdout_6 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_6_diverges : ∀ x, evalPRF holdout_6 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 7
-- M(C(R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2))),S,S))
def holdout_7 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ]

theorem holdout_7_diverges : ∀ x, evalPRF holdout_7 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 8
-- M(C(R(S,C(R(Z0,R(S,P(3,1))),P(3,2))),P(1,1),Z1))
def holdout_8 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1]

theorem holdout_8_diverges : ∀ x, evalPRF holdout_8 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 9
-- M(C(R(S,C(R(Z0,R(S,P(3,1))),P(3,2))),S,Z1))
def holdout_9 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)])) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_9_diverges : ∀ x, evalPRF holdout_9 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 10
-- M(C(R(S,R(P(2,1),R(R(P(2,2),P(4,1)),P(5,2)))),P(1,1),P(1,1)))
def holdout_10 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) ((PRF.proj 5 ⟨1, by decide⟩))))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_10_diverges : ∀ x, evalPRF holdout_10 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 11
-- M(C(R(S,R(P(2,1),R(R(P(2,2),P(4,1)),P(5,2)))),S,S))
def holdout_11 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))) ((PRF.proj 5 ⟨1, by decide⟩))))) prf_list![PRF.succ, PRF.succ]

theorem holdout_11_diverges : ∀ x, evalPRF holdout_11 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 12
-- M(C(R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2))),P(1,1),Z1))
def holdout_12 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1]

theorem holdout_12_diverges : ∀ x, evalPRF holdout_12 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 13
-- M(C(R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,Z1))
def holdout_13 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_13_diverges : ∀ x, evalPRF holdout_13 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 14
-- M(C(R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2))),S,P(1,1)))
def holdout_14 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_14_diverges : ∀ x, evalPRF holdout_14 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 15
-- M(R(C(S,Z0),R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1)))))
def holdout_15 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)]))

theorem holdout_15_diverges : ∀ x, evalPRF holdout_15 (fun _ => x) > 0 := by
  sorry

end Holdouts13
