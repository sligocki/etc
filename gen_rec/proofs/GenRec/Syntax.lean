import Mathlib

namespace GenRec

/-- A primitive recursive function of arity k -/
inductive PRF : Nat → Type
| zero (k : Nat) : PRF k
| succ : PRF 1
| proj (k : Nat) (i : Fin k) : PRF k
| comp {k m : Nat} (h : PRF m) (gs : Fin m → PRF k) : PRF k
| primRec {k : Nat} (g : PRF k) (h : PRF (k + 2)) : PRF (k + 1)

end GenRec
