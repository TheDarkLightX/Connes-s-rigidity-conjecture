import Mathlib

namespace LeanMathlib

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

/-- The `b`-part of `a`. -/
def leftSplit (a b : α) : α :=
  a ⊓ b

/-- The part of `a` outside `b`. -/
def rightSplit (a b : α) : α :=
  a \ b

theorem leftSplit_eq_inf (a b : α) : leftSplit a b = a ⊓ b := rfl

theorem rightSplit_eq_sdiff (a b : α) : rightSplit a b = a \ b := rfl

theorem rightSplit_eq_inf_compl (a b : α) : rightSplit a b = a ⊓ bᶜ := by
  simpa [rightSplit] using (sdiff_eq : a \ b = a ⊓ bᶜ)

theorem leftSplit_le_left (a b : α) : leftSplit a b ≤ a := by
  exact inf_le_left

theorem leftSplit_le_right (a b : α) : leftSplit a b ≤ b := by
  exact inf_le_right

theorem rightSplit_le_left (a b : α) : rightSplit a b ≤ a := by
  simp [rightSplit]

theorem leftSplit_disjoint_rightSplit (a b : α) :
    Disjoint (leftSplit a b) (rightSplit a b) := by
  have h : Disjoint b (a \ b) := (disjoint_sdiff_self_left : Disjoint (a \ b) b).symm
  exact h.mono_left (leftSplit_le_right a b)

theorem sup_leftSplit_rightSplit (a b : α) :
    leftSplit a b ⊔ rightSplit a b = a := by
  simp [leftSplit, rightSplit]

theorem sup_rightSplit_leftSplit (a b : α) :
    rightSplit a b ⊔ leftSplit a b = a := by
  rw [sup_comm, sup_leftSplit_rightSplit]

theorem rightSplit_eq_bot_iff (a b : α) :
    rightSplit a b = ⊥ ↔ a ≤ b := by
  simp [rightSplit]

theorem rightSplit_ne_bot_iff (a b : α) :
    rightSplit a b ≠ ⊥ ↔ ¬ a ≤ b := by
  rw [ne_eq, rightSplit_eq_bot_iff, not_iff_not]

theorem leftSplit_eq_bot_iff (a b : α) :
    leftSplit a b = ⊥ ↔ Disjoint a b := by
  simp [leftSplit, disjoint_iff]

theorem leftSplit_eq_self_iff (a b : α) :
    leftSplit a b = a ↔ a ≤ b := by
  simp [leftSplit, inf_eq_left]

theorem leftSplit_eq_right_of_le (a b : α) (h : b ≤ a) :
    leftSplit a b = b := by
  simp [leftSplit, inf_eq_right.mpr h]

theorem split_recompose_of_le (a b : α) (h : b ≤ a) :
    b ⊔ rightSplit a b = a := by
  calc
    b ⊔ rightSplit a b = leftSplit a b ⊔ rightSplit a b := by
      rw [leftSplit_eq_right_of_le a b h]
    _ = a := sup_leftSplit_rightSplit a b

end BooleanAlgebra

end LeanMathlib
