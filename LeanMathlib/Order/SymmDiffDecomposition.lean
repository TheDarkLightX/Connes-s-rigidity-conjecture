import LeanMathlib.Order.BooleanDecomposition
import Mathlib.Order.SymmDiff

namespace LeanMathlib

open scoped symmDiff

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

theorem symmDiff_eq_rightSplit_sup_rightSplit (a b : α) :
    a ∆ b = rightSplit a b ⊔ rightSplit b a := by
  simp [symmDiff_def, rightSplit]

theorem rightSplit_symmDiff_right (a b : α) :
    rightSplit (a ∆ b) b = rightSplit a b := by
  simp [rightSplit]

theorem rightSplit_symmDiff_left (a b : α) :
    rightSplit (a ∆ b) a = rightSplit b a := by
  simp [rightSplit]

theorem leftSplit_symmDiff_left_eq_rightSplit (a b : α) :
    leftSplit a (a ∆ b) = rightSplit a b := by
  calc
    leftSplit a (a ∆ b) = a ⊓ (a ∆ b) := rfl
    _ = (a ⊓ a) ∆ (a ⊓ b) := by
      simpa using (inf_symmDiff_distrib_left (a := a) (b := a) (c := b))
    _ = a ∆ (a ⊓ b) := by simp
    _ = a \ (a ⊓ b) := by
      rw [symmDiff_of_ge (show a ⊓ b ≤ a by exact inf_le_left)]
    _ = a \ b := by rw [inf_comm, sdiff_inf_self_right]
    _ = rightSplit a b := rfl

theorem leftSplit_symmDiff_right_eq_rightSplit (a b : α) :
    leftSplit b (a ∆ b) = rightSplit b a := by
  calc
    leftSplit b (a ∆ b) = leftSplit b (b ∆ a) := by rw [symmDiff_comm]
    _ = rightSplit b a := leftSplit_symmDiff_left_eq_rightSplit b a

theorem leftSplit_disjoint_symmDiff (a b : α) :
    Disjoint (leftSplit a b) (a ∆ b) := by
  simpa [leftSplit] using (disjoint_symmDiff_inf (a := a) (b := b)).symm

theorem sup_leftSplit_symmDiff (a b : α) :
    leftSplit a b ⊔ (a ∆ b) = a ⊔ b := by
  simp [leftSplit]

end BooleanAlgebra

end LeanMathlib
