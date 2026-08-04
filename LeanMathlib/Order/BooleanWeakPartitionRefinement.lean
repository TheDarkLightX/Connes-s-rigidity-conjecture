import LeanMathlib.Order.BooleanWeakPartition

namespace LeanMathlib

namespace WeakFourWayDecomposition

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]
variable {a w x y z u v : α}

theorem toWeakThreeWayLeftPair (h : WeakFourWayDecomposition a w x y z) :
    WeakThreeWayDecomposition a (w ⊔ x) y z where
  first_second := h.first_third.sup_left h.second_third
  first_third := h.first_fourth.sup_left h.second_fourth
  second_third := h.third_fourth
  sup_eq := h.sup_eq

theorem toWeakThreeWayMiddlePair (h : WeakFourWayDecomposition a w x y z) :
    WeakThreeWayDecomposition a w (x ⊔ y) z where
  first_second := h.first_second.sup_right h.first_third
  first_third := h.first_fourth
  second_third := h.second_fourth.sup_left h.third_fourth
  sup_eq := by
    calc
      (w ⊔ (x ⊔ y)) ⊔ z = ((w ⊔ x) ⊔ y) ⊔ z := by ac_rfl
      _ = a := h.sup_eq

theorem toWeakThreeWayRightPair (h : WeakFourWayDecomposition a w x y z) :
    WeakThreeWayDecomposition a w x (y ⊔ z) where
  first_second := h.first_second
  first_third := h.first_third.sup_right h.first_fourth
  second_third := h.second_third.sup_right h.second_fourth
  sup_eq := by
    calc
      (w ⊔ x) ⊔ (y ⊔ z) = ((w ⊔ x) ⊔ y) ⊔ z := by ac_rfl
      _ = a := h.sup_eq

theorem toWeakTwoWayPairPair (h : WeakFourWayDecomposition a w x y z) :
    WeakTwoWayDecomposition a (w ⊔ x) (y ⊔ z) where
  disjoint := (h.first_third.sup_right h.first_fourth).sup_left
    (h.second_third.sup_right h.second_fourth)
  sup_eq := by
    calc
      (w ⊔ x) ⊔ (y ⊔ z) = ((w ⊔ x) ⊔ y) ⊔ z := by ac_rfl
      _ = a := h.sup_eq

theorem toWeakTwoWayFirstRest (h : WeakFourWayDecomposition a w x y z) :
    WeakTwoWayDecomposition a w ((x ⊔ y) ⊔ z) where
  disjoint := (h.first_second.sup_right h.first_third).sup_right h.first_fourth
  sup_eq := by
    calc
      w ⊔ ((x ⊔ y) ⊔ z) = ((w ⊔ x) ⊔ y) ⊔ z := by ac_rfl
      _ = a := h.sup_eq

theorem commonRefinement_first_row_eq
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    (x ⊓ u) ⊔ (x ⊓ v) = x := by
  calc
    (x ⊓ u) ⊔ (x ⊓ v) = x ⊓ (u ⊔ v) := by rw [← inf_sup_left]
    _ = x ⊓ a := by rw [h₂.sup_eq]
    _ = x := inf_eq_left.mpr h₁.left_le_total

theorem commonRefinement_second_row_eq
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    (y ⊓ u) ⊔ (y ⊓ v) = y := by
  calc
    (y ⊓ u) ⊔ (y ⊓ v) = y ⊓ (u ⊔ v) := by rw [← inf_sup_left]
    _ = y ⊓ a := by rw [h₂.sup_eq]
    _ = y := inf_eq_left.mpr h₁.right_le_total

theorem commonRefinement_first_col_eq
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    (x ⊓ u) ⊔ (y ⊓ u) = u := by
  calc
    (x ⊓ u) ⊔ (y ⊓ u) = (x ⊔ y) ⊓ u := by rw [← inf_sup_right]
    _ = a ⊓ u := by rw [h₁.sup_eq]
    _ = u := inf_eq_right.mpr h₂.left_le_total

theorem commonRefinement_second_col_eq
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    (x ⊓ v) ⊔ (y ⊓ v) = v := by
  calc
    (x ⊓ v) ⊔ (y ⊓ v) = (x ⊔ y) ⊓ v := by rw [← inf_sup_right]
    _ = a ⊓ v := by rw [h₁.sup_eq]
    _ = v := inf_eq_right.mpr h₂.right_le_total

theorem commonRefinement_rowPartition
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    WeakTwoWayDecomposition a
      ((x ⊓ u) ⊔ (x ⊓ v)) ((y ⊓ u) ⊔ (y ⊓ v)) := by
  simpa [commonRefinement_first_row_eq h₁ h₂, commonRefinement_second_row_eq h₁ h₂] using h₁

theorem commonRefinement_colPartition
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    WeakTwoWayDecomposition a
      ((x ⊓ u) ⊔ (y ⊓ u)) ((x ⊓ v) ⊔ (y ⊓ v)) := by
  simpa [commonRefinement_first_col_eq h₁ h₂, commonRefinement_second_col_eq h₁ h₂] using h₂

end BooleanAlgebra

end WeakFourWayDecomposition

end LeanMathlib
