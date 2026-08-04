import LeanMathlib.Order.AtomlessOrderDensity

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/--
Every strict interval in an atomless Boolean algebra contains a strict
two-step chain.
-/
theorem exists_two_between_of_lt {a b : α} (hab : a < b) :
    ∃ c d : α, a < c ∧ c < d ∧ d < b := by
  obtain ⟨c, hac, hcb⟩ := exists_between_of_lt hab
  obtain ⟨d, hcd, hdb⟩ := exists_between_of_lt hcb
  exact ⟨c, d, hac, hcd, hdb⟩

/--
Every strict interval in an atomless Boolean algebra contains a strict
three-step chain.
-/
theorem exists_three_between_of_lt {a b : α} (hab : a < b) :
    ∃ c d e : α, a < c ∧ c < d ∧ d < e ∧ e < b := by
  obtain ⟨c, d, hac, hcd, hdb⟩ := exists_two_between_of_lt hab
  obtain ⟨e, hde, heb⟩ := exists_between_of_lt hdb
  exact ⟨c, d, e, hac, hcd, hde, heb⟩

end Atomless

end LeanMathlib
