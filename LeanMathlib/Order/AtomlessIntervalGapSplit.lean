import LeanMathlib.Order.AtomlessOrderDensity

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/--
Every strict interval in an atomless Boolean algebra has an intermediate point
whose lower and upper Boolean gaps are both nonzero.
-/
theorem exists_between_with_nonzero_rightSplits {a b : α} (hab : a < b) :
    ∃ c : α,
      a < c ∧ c < b ∧ rightSplit c a ≠ ⊥ ∧ rightSplit b c ≠ ⊥ := by
  obtain ⟨c, hac, hcb⟩ := exists_between_of_lt hab
  exact ⟨c, hac, hcb, exists_nonzero_rightSplit hac, exists_nonzero_rightSplit hcb⟩

/--
Every strict interval decomposes through an intermediate point into two
nonzero disjoint Boolean gaps.
-/
theorem exists_interval_gap_decomposition {a b : α} (hab : a < b) :
    ∃ c lower upper : α,
      a < c ∧ c < b ∧
      lower ≠ ⊥ ∧ upper ≠ ⊥ ∧ Disjoint lower upper ∧
      a ⊔ lower = c ∧ c ⊔ upper = b := by
  obtain ⟨c, hac, hcb, hlower0, hupper0⟩ :=
    exists_between_with_nonzero_rightSplits hab
  refine ⟨c, rightSplit c a, rightSplit b c, hac, hcb, hlower0, hupper0, ?_, ?_, ?_⟩
  · have hupper_disj : Disjoint c (rightSplit b c) := by
      have hsplit := leftSplit_disjoint_rightSplit b c
      simpa [leftSplit_eq_right_of_le b c hcb.le] using hsplit
    exact hupper_disj.mono_left (rightSplit_le_left c a)
  · exact split_recompose_of_le c a hac.le
  · exact split_recompose_of_le b c hcb.le

end Atomless

end LeanMathlib
