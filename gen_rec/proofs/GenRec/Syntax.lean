import Mathlib

namespace GenRec

mutual
/-- A primitive recursive function of arity k -/
inductive PRF : Nat → Type
| zero (k : Nat) : PRF k
| succ : PRF 1
| proj (k : Nat) (i : Fin k) : PRF k
| comp {k m : Nat} (h : PRF m) (gs : PRFList k m) : PRF k
| primRec {k : Nat} (g : PRF k) (h : PRF (k + 2)) : PRF (k + 1)

/-- A list of PRFs, all sharing the same input arity k -/
inductive PRFList : Nat → Nat → Type
| nil {k : Nat} : PRFList k 0
| cons {k m : Nat} : PRF k → PRFList k m → PRFList k (m + 1)
end

syntax "prf_list![" term,* "]" : term
macro_rules
  | `(prf_list![]) => `(PRFList.nil)
  | `(prf_list![$x]) => `(PRFList.cons $x PRFList.nil)
  | `(prf_list![$x, $xs:term,*]) => `(PRFList.cons $x prf_list![$xs,*])

end GenRec
