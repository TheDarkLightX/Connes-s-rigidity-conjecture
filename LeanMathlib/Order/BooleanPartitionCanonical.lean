import LeanMathlib.Order.BooleanPartition

namespace LeanMathlib

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

namespace TwoWayDecomposition

variable {a x y z : α}

theorem rightSplit_total_left (h : TwoWayDecomposition a x y) :
    rightSplit a x = y := by
  simpa [rightSplit] using h.disjoint.sdiff_eq_of_sup_eq h.sup_eq

theorem rightSplit_total_right (h : TwoWayDecomposition a x y) :
    rightSplit a y = x := by
  exact h.symm.rightSplit_total_left

theorem leftSplit_total_left (h : TwoWayDecomposition a x y) :
    leftSplit a x = x :=
  leftSplit_eq_right_of_le a x h.left_le_total

theorem leftSplit_total_right (h : TwoWayDecomposition a x y) :
    leftSplit a y = y :=
  leftSplit_eq_right_of_le a y h.right_le_total

theorem right_eq_of_same_left
    (h₁ : TwoWayDecomposition a x y) (h₂ : TwoWayDecomposition a x z) :
    y = z := by
  rw [← h₁.rightSplit_total_left, ← h₂.rightSplit_total_left]

theorem left_eq_of_same_right
    (h₁ : TwoWayDecomposition a x z) (h₂ : TwoWayDecomposition a y z) :
    x = y := by
  rw [← h₁.rightSplit_total_right, ← h₂.rightSplit_total_right]

end TwoWayDecomposition

namespace ThreeWayDecomposition

variable {a x y z : α}

theorem rightSplit_total_firstPair (h : ThreeWayDecomposition a x y z) :
    rightSplit a (x ⊔ y) = z :=
  h.toTwoWayLeft.rightSplit_total_left

theorem rightSplit_total_first (h : ThreeWayDecomposition a x y z) :
    rightSplit a x = y ⊔ z :=
  h.toTwoWayRight.rightSplit_total_left

theorem rightSplit_firstRemainder_second (h : ThreeWayDecomposition a x y z) :
    rightSplit (rightSplit a x) y = z := by
  have hyz : TwoWayDecomposition (y ⊔ z) y z :=
    { left_nonzero := h.second_nonzero
      right_nonzero := h.third_nonzero
      disjoint := h.second_third
      sup_eq := rfl }
  calc
    rightSplit (rightSplit a x) y = rightSplit (y ⊔ z) y := by
      rw [h.rightSplit_total_first]
    _ = z := hyz.rightSplit_total_left

theorem leftSplit_total_first (h : ThreeWayDecomposition a x y z) :
    leftSplit a x = x :=
  h.toTwoWayRight.leftSplit_total_left

theorem leftSplit_total_firstPair (h : ThreeWayDecomposition a x y z) :
    leftSplit a (x ⊔ y) = x ⊔ y :=
  h.toTwoWayLeft.leftSplit_total_left

end ThreeWayDecomposition

end BooleanAlgebra

end LeanMathlib
