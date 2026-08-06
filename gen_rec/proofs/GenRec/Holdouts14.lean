import GenRec.Syntax
import GenRec.Semantics

open GenRec

namespace Holdouts14

-- Translating holdout 1
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_1 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_1_diverges : ∀ x, evalPRF holdout_1 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 2
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_2 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_2_diverges : ∀ x, evalPRF holdout_2 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 3
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),P(1,1)))
def holdout_3 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_3_diverges : ∀ x, evalPRF holdout_3 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 4
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_4 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_4_diverges : ∀ x, evalPRF holdout_4 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 5
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),P(1,1)))
def holdout_5 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_5_diverges : ∀ x, evalPRF holdout_5 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 6
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),P(3,1))),R(Z0,P(2,1)),S))
def holdout_6 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩)), PRF.succ]

theorem holdout_6_diverges : ∀ x, evalPRF holdout_6 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 7
-- M(C(R(P(2,1),R(P(3,1),R(R(P(3,3),P(5,1)),P(6,2)))),P(1,1),S,P(1,1)))
def holdout_7 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 3 ⟨2, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩))) ((PRF.proj 6 ⟨1, by decide⟩))))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_7_diverges : ∀ x, evalPRF holdout_7 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 8
-- M(C(R(P(2,1),R(R(P(2,1),R(P(3,3),P(5,1))),P(5,2))),S,S,S))
def holdout_8 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨2, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, PRF.succ]

theorem holdout_8_diverges : ∀ x, evalPRF holdout_8 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 9
-- M(C(R(P(2,1),R(R(P(2,2),R(Z3,P(5,1))),P(5,2))),S,P(1,1),S))
def holdout_9 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec (PRF.zero 3) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_9_diverges : ∀ x, evalPRF holdout_9 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 10
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,1),P(5,1))),P(5,2))),S,S,S))
def holdout_10 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨0, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, PRF.succ]

theorem holdout_10_diverges : ∀ x, evalPRF holdout_10 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 11
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,P(1,1),S))
def holdout_11 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨1, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_11_diverges : ∀ x, evalPRF holdout_11 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 12
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,S,P(1,1)))
def holdout_12 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨1, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_12_diverges : ∀ x, evalPRF holdout_12 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 13
-- M(C(R(P(2,1),R(R(P(2,2),R(P(3,2),P(5,1))),P(5,2))),S,S,S))
def holdout_13 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.primRec ((PRF.proj 3 ⟨1, by decide⟩)) ((PRF.proj 5 ⟨0, by decide⟩)))) ((PRF.proj 5 ⟨1, by decide⟩)))) prf_list![PRF.succ, PRF.succ, PRF.succ]

theorem holdout_13_diverges : ∀ x, evalPRF holdout_13 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 14
-- M(C(R(Z1,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_14 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_14_diverges : ∀ x, evalPRF holdout_14 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 15
-- M(C(R(Z1,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,P(1,1)))
def holdout_15 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_15_diverges : ∀ x, evalPRF holdout_15 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 16
-- M(C(R(Z1,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_16 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_16_diverges : ∀ x, evalPRF holdout_16 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 17
-- M(C(R(Z1,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def holdout_17 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_17_diverges : ∀ x, evalPRF holdout_17 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 18
-- M(C(R(Z1,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),S,S))
def holdout_18 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_18_diverges : ∀ x, evalPRF holdout_18 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 19
-- M(C(R(Z1,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_19 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_19_diverges : ∀ x, evalPRF holdout_19 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 20
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),S,S))
def holdout_20 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_20_diverges : ∀ x, evalPRF holdout_20 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 21
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def holdout_21 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_21_diverges : ∀ x, evalPRF holdout_21 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 22
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_22 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_22_diverges : ∀ x, evalPRF holdout_22 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 23
-- M(C(R(Z1,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_23 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_23_diverges : ∀ x, evalPRF holdout_23 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 24
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_24 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_24_diverges : ∀ x, evalPRF holdout_24 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 25
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_25 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_25_diverges : ∀ x, evalPRF holdout_25 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 26
-- M(C(R(P(1,1),C(R(P(1,1),P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_26 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_26_diverges : ∀ x, evalPRF holdout_26 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 27
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_27 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_27_diverges : ∀ x, evalPRF holdout_27 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 28
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),S,P(1,1)))
def holdout_28 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_28_diverges : ∀ x, evalPRF holdout_28 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 29
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_29 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_29_diverges : ∀ x, evalPRF holdout_29 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 30
-- M(C(R(P(1,1),C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,P(1,1)))
def holdout_30 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_30_diverges : ∀ x, evalPRF holdout_30 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 31
-- M(C(R(P(1,1),C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_31 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_31_diverges : ∀ x, evalPRF holdout_31 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 32
-- M(C(R(P(1,1),C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def holdout_32 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_32_diverges : ∀ x, evalPRF holdout_32 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 33
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,Z1))
def holdout_33 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_33_diverges : ∀ x, evalPRF holdout_33 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 34
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,P(1,1)))
def holdout_34 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_34_diverges : ∀ x, evalPRF holdout_34 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 35
-- M(C(R(P(1,1),C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,S))
def holdout_35 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.succ]

theorem holdout_35_diverges : ∀ x, evalPRF holdout_35 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 36
-- M(C(R(P(1,1),C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),S))
def holdout_36 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_36_diverges : ∀ x, evalPRF holdout_36 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 37
-- M(C(R(P(1,1),R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_37 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_37_diverges : ∀ x, evalPRF holdout_37 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 38
-- M(C(R(P(1,1),R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_38 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_38_diverges : ∀ x, evalPRF holdout_38 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 39
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_39 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_39_diverges : ∀ x, evalPRF holdout_39 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 40
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_40 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_40_diverges : ∀ x, evalPRF holdout_40 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 41
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_41 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_41_diverges : ∀ x, evalPRF holdout_41 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 42
-- M(C(R(P(1,1),R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_42 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_42_diverges : ∀ x, evalPRF holdout_42 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 43
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_43 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_43_diverges : ∀ x, evalPRF holdout_43 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 44
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_44 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_44_diverges : ∀ x, evalPRF holdout_44 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 45
-- M(C(R(P(1,1),R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_45 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_45_diverges : ∀ x, evalPRF holdout_45 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 46
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_46 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_46_diverges : ∀ x, evalPRF holdout_46 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 47
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),S))
def holdout_47 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_47_diverges : ∀ x, evalPRF holdout_47 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 48
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def holdout_48 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_48_diverges : ∀ x, evalPRF holdout_48 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 49
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_49 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_49_diverges : ∀ x, evalPRF holdout_49 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 50
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_50 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_50_diverges : ∀ x, evalPRF holdout_50 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 51
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_51 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_51_diverges : ∀ x, evalPRF holdout_51 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 52
-- M(C(R(P(1,1),R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_52 : PRF 1 :=
  PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_52_diverges : ∀ x, evalPRF holdout_52 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 53
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),P(1,1)))
def holdout_53 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_53_diverges : ∀ x, evalPRF holdout_53 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 54
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_54 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_54_diverges : ∀ x, evalPRF holdout_54 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 55
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(Z2,P(4,1)))),S,S))
def holdout_55 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_55_diverges : ∀ x, evalPRF holdout_55 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 56
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_56 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_56_diverges : ∀ x, evalPRF holdout_56 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 57
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_57 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_57_diverges : ∀ x, evalPRF holdout_57 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 58
-- M(C(R(S,C(R(P(1,1),P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_58 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_58_diverges : ∀ x, evalPRF holdout_58 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 59
-- M(C(R(S,C(R(P(1,1),P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_59 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_59_diverges : ∀ x, evalPRF holdout_59 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 60
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),P(1,1)))
def holdout_60 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_60_diverges : ∀ x, evalPRF holdout_60 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 61
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),P(1,1),S))
def holdout_61 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_61_diverges : ∀ x, evalPRF holdout_61 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 62
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(Z2,P(4,1)))),S,S))
def holdout_62 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec (PRF.zero 2) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_62_diverges : ∀ x, evalPRF holdout_62 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 63
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_63 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_63_diverges : ∀ x, evalPRF holdout_63 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 64
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),P(1,1),S))
def holdout_64 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_64_diverges : ∀ x, evalPRF holdout_64 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 65
-- M(C(R(S,C(R(S,P(3,1)),P(3,2),R(P(2,2),P(4,1)))),S,S))
def holdout_65 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩))])) prf_list![PRF.succ, PRF.succ]

theorem holdout_65_diverges : ∀ x, evalPRF holdout_65 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 66
-- M(C(R(S,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),P(1,1),S))
def holdout_66 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_66_diverges : ∀ x, evalPRF holdout_66 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 67
-- M(C(R(S,C(R(S,P(3,1)),R(P(2,2),P(4,3)),P(3,1))),S,P(1,1)))
def holdout_67 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨2, by decide⟩)), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_67_diverges : ∀ x, evalPRF holdout_67 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 68
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),P(1,1),Z1))
def holdout_68 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.zero 1]

theorem holdout_68_diverges : ∀ x, evalPRF holdout_68 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 69
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,Z1))
def holdout_69 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, PRF.zero 1]

theorem holdout_69_diverges : ∀ x, evalPRF holdout_69 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 70
-- M(C(R(S,C(R(S,R(P(2,1),P(4,1))),P(3,2),Z3)),S,P(1,1)))
def holdout_70 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), PRF.zero 3])) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_70_diverges : ∀ x, evalPRF holdout_70 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 71
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),P(1,1)))
def holdout_71 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_71_diverges : ∀ x, evalPRF holdout_71 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 72
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),P(1,1),S))
def holdout_72 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_72_diverges : ∀ x, evalPRF holdout_72 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 73
-- M(C(R(S,C(R(R(Z0,P(2,1)),P(3,1)),P(3,2),P(3,1))),S,S))
def holdout_73 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.comp (PRF.primRec (PRF.primRec (PRF.zero 0) ((PRF.proj 2 ⟨0, by decide⟩))) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 3 ⟨1, by decide⟩), (PRF.proj 3 ⟨0, by decide⟩)])) prf_list![PRF.succ, PRF.succ]

theorem holdout_73_diverges : ∀ x, evalPRF holdout_73 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 74
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_74 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_74_diverges : ∀ x, evalPRF holdout_74 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 75
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_75 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_75_diverges : ∀ x, evalPRF holdout_75 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 76
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,P(1,1)))
def holdout_76 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_76_diverges : ∀ x, evalPRF holdout_76 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 77
-- M(C(R(S,R(P(2,1),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_77 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_77_diverges : ∀ x, evalPRF holdout_77 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 78
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_78 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_78_diverges : ∀ x, evalPRF holdout_78 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 79
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_79 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_79_diverges : ∀ x, evalPRF holdout_79 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 80
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,P(1,1)))
def holdout_80 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_80_diverges : ∀ x, evalPRF holdout_80 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 81
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_81 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_81_diverges : ∀ x, evalPRF holdout_81 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 82
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),P(1,1)))
def holdout_82 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_82_diverges : ∀ x, evalPRF holdout_82 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 83
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_83 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_83_diverges : ∀ x, evalPRF holdout_83 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 84
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,P(1,1)))
def holdout_84 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_84_diverges : ∀ x, evalPRF holdout_84 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 85
-- M(C(R(S,R(P(2,1),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_85 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_85_diverges : ∀ x, evalPRF holdout_85 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 86
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_86 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_86_diverges : ∀ x, evalPRF holdout_86 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 87
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_87 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_87_diverges : ∀ x, evalPRF holdout_87 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 88
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_88 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_88_diverges : ∀ x, evalPRF holdout_88 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 89
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_89 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_89_diverges : ∀ x, evalPRF holdout_89 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 90
-- M(C(R(S,R(P(2,2),C(R(P(1,1),P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_90 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_90_diverges : ∀ x, evalPRF holdout_90 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 91
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),P(1,1)))
def holdout_91 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_91_diverges : ∀ x, evalPRF holdout_91 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 92
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,1)))),P(1,1),S))
def holdout_92 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_92_diverges : ∀ x, evalPRF holdout_92 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 93
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),P(1,1)))
def holdout_93 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_93_diverges : ∀ x, evalPRF holdout_93 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 94
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),P(1,1),S))
def holdout_94 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_94_diverges : ∀ x, evalPRF holdout_94 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 95
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,2),P(4,3)))),S,S))
def holdout_95 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨1, by decide⟩), (PRF.proj 4 ⟨2, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_95_diverges : ∀ x, evalPRF holdout_95 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 96
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),P(1,1)))
def holdout_96 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_96_diverges : ∀ x, evalPRF holdout_96 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 97
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),P(1,1),S))
def holdout_97 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_97_diverges : ∀ x, evalPRF holdout_97 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 98
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,1)))),S,S))
def holdout_98 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨0, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_98_diverges : ∀ x, evalPRF holdout_98 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 99
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),P(1,1)))
def holdout_99 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), (PRF.proj 1 ⟨0, by decide⟩)]

theorem holdout_99_diverges : ∀ x, evalPRF holdout_99 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 100
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),P(1,1),S))
def holdout_100 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![(PRF.proj 1 ⟨0, by decide⟩), PRF.succ]

theorem holdout_100_diverges : ∀ x, evalPRF holdout_100 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 101
-- M(C(R(S,R(P(2,2),C(R(S,P(3,1)),P(4,3),P(4,2)))),S,S))
def holdout_101 : PRF 1 :=
  PRF.comp (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) (PRF.comp (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩))) prf_list![(PRF.proj 4 ⟨2, by decide⟩), (PRF.proj 4 ⟨1, by decide⟩)]))) prf_list![PRF.succ, PRF.succ]

theorem holdout_101_diverges : ∀ x, evalPRF holdout_101 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 102
-- M(R(C(S,Z0),R(P(1,1),C(R(Z0,R(S,P(3,1))),P(3,2)))))
def holdout_102 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.comp (PRF.primRec (PRF.zero 0) (PRF.primRec (PRF.succ) ((PRF.proj 3 ⟨0, by decide⟩)))) prf_list![(PRF.proj 3 ⟨1, by decide⟩)]))

theorem holdout_102_diverges : ∀ x, evalPRF holdout_102 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 103
-- M(R(C(S,Z0),R(P(1,1),R(R(Z1,R(P(2,2),P(4,1))),P(4,2)))))
def holdout_103 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.zero 1) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_103_diverges : ∀ x, evalPRF holdout_103 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 104
-- M(R(C(S,Z0),R(P(1,1),R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2)))))
def holdout_104 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_104_diverges : ∀ x, evalPRF holdout_104 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 105
-- M(R(C(S,Z0),R(P(1,1),R(R(S,R(P(2,1),P(4,1))),P(4,2)))))
def holdout_105 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_105_diverges : ∀ x, evalPRF holdout_105 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 106
-- M(R(C(S,Z0),R(P(1,1),R(R(S,R(P(2,2),P(4,1))),P(4,2)))))
def holdout_106 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨1, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_106_diverges : ∀ x, evalPRF holdout_106 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 107
-- M(R(C(S,Z0),R(S,R(R(P(1,1),R(P(2,1),P(4,1))),P(4,2)))))
def holdout_107 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec ((PRF.proj 1 ⟨0, by decide⟩)) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_107_diverges : ∀ x, evalPRF holdout_107 (fun _ => x) > 0 := by
  sorry

-- Translating holdout 108
-- M(R(C(S,Z0),R(S,R(R(S,R(P(2,1),P(4,1))),P(4,2)))))
def holdout_108 : PRF 1 :=
  PRF.primRec (PRF.comp (PRF.succ) prf_list![PRF.zero 0]) (PRF.primRec (PRF.succ) (PRF.primRec (PRF.primRec (PRF.succ) (PRF.primRec ((PRF.proj 2 ⟨0, by decide⟩)) ((PRF.proj 4 ⟨0, by decide⟩)))) ((PRF.proj 4 ⟨1, by decide⟩))))

theorem holdout_108_diverges : ∀ x, evalPRF holdout_108 (fun _ => x) > 0 := by
  sorry

end Holdouts14
