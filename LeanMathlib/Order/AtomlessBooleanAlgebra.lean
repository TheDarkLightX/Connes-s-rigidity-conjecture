import LeanMathlib.Order.BooleanDecomposition
import Mathlib.Order.Atoms

namespace LeanMathlib

section BooleanAlgebra

variable (α : Type*) [BooleanAlgebra α]

/--
An atomless Boolean algebra: every nonzero element has a proper nonzero part.

This is the refinement property needed for reusable splitting constructions.
-/
class IsAtomless : Prop where
  exists_lt_nonzero : ∀ {a : α}, a ≠ ⊥ → ∃ b : α, b ≠ ⊥ ∧ b < a

end BooleanAlgebra

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

theorem exists_lt_nonzero {a : α} (ha : a ≠ ⊥) :
    ∃ b : α, b ≠ ⊥ ∧ b < a :=
  IsAtomless.exists_lt_nonzero ha

theorem not_isAtom {a : α} (ha0 : a ≠ ⊥) : ¬ IsAtom a := by
  intro ha
  obtain ⟨b, hb0, hba⟩ := exists_lt_nonzero ha0
  have hb_eq : b = a := (ha.ne_bot_iff_eq hba.le).1 hb0
  exact hba.ne hb_eq

omit [IsAtomless α] in
theorem exists_nonzero_rightSplit {a b : α} (hba : b < a) :
    rightSplit a b ≠ ⊥ := by
  intro hsplit
  have hab : a ≤ b := (rightSplit_eq_bot_iff a b).1 hsplit
  exact hba.ne (le_antisymm hba.le hab)

theorem exists_nontrivial_split {a : α} (ha : a ≠ ⊥) :
    ∃ b c : α, b ≠ ⊥ ∧ c ≠ ⊥ ∧ Disjoint b c ∧ b ⊔ c = a := by
  obtain ⟨b, hb0, hba⟩ := exists_lt_nonzero ha
  refine ⟨b, rightSplit a b, hb0, exists_nonzero_rightSplit hba, ?_, ?_⟩
  · have hdisj : Disjoint (leftSplit a b) (rightSplit a b) :=
      leftSplit_disjoint_rightSplit a b
    simpa [leftSplit_eq_right_of_le a b hba.le] using hdisj
  · exact split_recompose_of_le a b hba.le

theorem exists_nontrivial_meet_compl {a : α} (ha : a ≠ ⊥) :
    ∃ b : α, a ⊓ b ≠ ⊥ ∧ a ⊓ bᶜ ≠ ⊥ := by
  obtain ⟨b, hb0, hba⟩ := exists_lt_nonzero ha
  refine ⟨b, ?_, ?_⟩
  · simpa [inf_eq_right.mpr hba.le] using hb0
  · simpa [rightSplit_eq_inf_compl] using exists_nonzero_rightSplit hba

theorem top_not_isAtom [Nontrivial α] : ¬ IsAtom (⊤ : α) := by
  exact not_isAtom (show (⊤ : α) ≠ ⊥ from top_ne_bot)

theorem not_isAtomic [Nontrivial α] : ¬ IsAtomic α := by
  intro hAtomic
  let _ : IsAtomic α := hAtomic
  obtain ⟨a, ha⟩ := IsAtomic.exists_atom (α := α)
  exact not_isAtom ha.ne_bot ha

end Atomless

end LeanMathlib
