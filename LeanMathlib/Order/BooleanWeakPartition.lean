import LeanMathlib.Order.BooleanPartitionCanonical

namespace LeanMathlib

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

/-- A two-way Boolean decomposition certificate allowing zero pieces. -/
structure WeakTwoWayDecomposition (a x y : α) : Prop where
  disjoint : Disjoint x y
  sup_eq : x ⊔ y = a

/-- A three-way Boolean decomposition certificate allowing zero pieces. -/
structure WeakThreeWayDecomposition (a x y z : α) : Prop where
  first_second : Disjoint x y
  first_third : Disjoint x z
  second_third : Disjoint y z
  sup_eq : (x ⊔ y) ⊔ z = a

/-- A four-way Boolean decomposition certificate allowing zero pieces. -/
structure WeakFourWayDecomposition (a w x y z : α) : Prop where
  first_second : Disjoint w x
  first_third : Disjoint w y
  first_fourth : Disjoint w z
  second_third : Disjoint x y
  second_fourth : Disjoint x z
  third_fourth : Disjoint y z
  sup_eq : ((w ⊔ x) ⊔ y) ⊔ z = a

namespace WeakTwoWayDecomposition

variable {a x y z r : α}

theorem ofStrong (h : TwoWayDecomposition a x y) :
    WeakTwoWayDecomposition a x y where
  disjoint := h.disjoint
  sup_eq := h.sup_eq

theorem toStrong (h : WeakTwoWayDecomposition a x y) (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    TwoWayDecomposition a x y where
  left_nonzero := hx
  right_nonzero := hy
  disjoint := h.disjoint
  sup_eq := h.sup_eq

theorem symm (h : WeakTwoWayDecomposition a x y) :
    WeakTwoWayDecomposition a y x where
  disjoint := h.disjoint.symm
  sup_eq := by rw [sup_comm, h.sup_eq]

theorem left_le_total (h : WeakTwoWayDecomposition a x y) : x ≤ a := by
  rw [← h.sup_eq]
  exact le_sup_left

theorem right_le_total (h : WeakTwoWayDecomposition a x y) : y ≤ a := by
  rw [← h.sup_eq]
  exact le_sup_right

theorem rightSplit_total_left (h : WeakTwoWayDecomposition a x y) :
    rightSplit a x = y := by
  simpa [rightSplit] using h.disjoint.sdiff_eq_of_sup_eq h.sup_eq

theorem rightSplit_total_right (h : WeakTwoWayDecomposition a x y) :
    rightSplit a y = x :=
  h.symm.rightSplit_total_left

theorem of_rightSplit_of_le {a b : α} (hba : b ≤ a) :
    WeakTwoWayDecomposition a b (rightSplit a b) where
  disjoint := by
    have hdisj : Disjoint (leftSplit a b) (rightSplit a b) :=
      leftSplit_disjoint_rightSplit a b
    simpa [leftSplit_eq_right_of_le a b hba] using hdisj
  sup_eq := split_recompose_of_le a b hba

end WeakTwoWayDecomposition

namespace WeakThreeWayDecomposition

variable {a x y z r : α}

theorem ofStrong (h : ThreeWayDecomposition a x y z) :
    WeakThreeWayDecomposition a x y z where
  first_second := h.first_second
  first_third := h.first_third
  second_third := h.second_third
  sup_eq := h.sup_eq

theorem toStrong (h : WeakThreeWayDecomposition a x y z)
    (hx : x ≠ ⊥) (hy : y ≠ ⊥) (hz : z ≠ ⊥) :
    ThreeWayDecomposition a x y z where
  first_nonzero := hx
  second_nonzero := hy
  third_nonzero := hz
  first_second := h.first_second
  first_third := h.first_third
  second_third := h.second_third
  sup_eq := h.sup_eq

theorem toWeakTwoWayLeft (h : WeakThreeWayDecomposition a x y z) :
    WeakTwoWayDecomposition a (x ⊔ y) z where
  disjoint := h.first_third.sup_left h.second_third
  sup_eq := h.sup_eq

theorem toWeakTwoWayRight (h : WeakThreeWayDecomposition a x y z) :
    WeakTwoWayDecomposition a x (y ⊔ z) where
  disjoint := h.first_second.sup_right h.first_third
  sup_eq := by
    calc
      x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by rw [sup_assoc]
      _ = a := h.sup_eq

theorem ofNested
    (outer : WeakTwoWayDecomposition a x r) (inner : WeakTwoWayDecomposition r y z) :
    WeakThreeWayDecomposition a x y z where
  first_second := outer.disjoint.mono_right inner.left_le_total
  first_third := outer.disjoint.mono_right inner.right_le_total
  second_third := inner.disjoint
  sup_eq := by
    calc
      (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) := by rw [sup_assoc]
      _ = x ⊔ r := by rw [inner.sup_eq]
      _ = a := outer.sup_eq

end WeakThreeWayDecomposition

namespace WeakFourWayDecomposition

variable {a w x y z u v : α}

theorem toWeakTwoWayLeft (h : WeakFourWayDecomposition a w x y z) :
    WeakTwoWayDecomposition a ((w ⊔ x) ⊔ y) z where
  disjoint := (h.first_fourth.sup_left h.second_fourth).sup_left h.third_fourth
  sup_eq := h.sup_eq

theorem commonRefinement
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v) :
    WeakFourWayDecomposition a (x ⊓ u) (x ⊓ v) (y ⊓ u) (y ⊓ v) where
  first_second :=
    (h₂.disjoint.mono_left (inf_le_right : x ⊓ u ≤ u)).mono_right
      (inf_le_right : x ⊓ v ≤ v)
  first_third :=
    (h₁.disjoint.mono_left (inf_le_left : x ⊓ u ≤ x)).mono_right
      (inf_le_left : y ⊓ u ≤ y)
  first_fourth :=
    (h₁.disjoint.mono_left (inf_le_left : x ⊓ u ≤ x)).mono_right
      (inf_le_left : y ⊓ v ≤ y)
  second_third :=
    (h₁.disjoint.mono_left (inf_le_left : x ⊓ v ≤ x)).mono_right
      (inf_le_left : y ⊓ u ≤ y)
  second_fourth :=
    (h₁.disjoint.mono_left (inf_le_left : x ⊓ v ≤ x)).mono_right
      (inf_le_left : y ⊓ v ≤ y)
  third_fourth :=
    (h₂.disjoint.mono_left (inf_le_right : y ⊓ u ≤ u)).mono_right
      (inf_le_right : y ⊓ v ≤ v)
  sup_eq := by
    have hx_le : x ≤ a := h₁.left_le_total
    have hy_le : y ≤ a := h₁.right_le_total
    calc
      (((x ⊓ u) ⊔ (x ⊓ v)) ⊔ (y ⊓ u)) ⊔ (y ⊓ v)
          = ((x ⊓ u) ⊔ (x ⊓ v)) ⊔ ((y ⊓ u) ⊔ (y ⊓ v)) := by
            ac_rfl
      _ = (x ⊓ (u ⊔ v)) ⊔ (y ⊓ (u ⊔ v)) := by
            rw [← inf_sup_left, ← inf_sup_left]
      _ = (x ⊓ a) ⊔ (y ⊓ a) := by rw [h₂.sup_eq]
      _ = x ⊔ y := by rw [inf_eq_left.mpr hx_le, inf_eq_left.mpr hy_le]
      _ = a := h₁.sup_eq

end WeakFourWayDecomposition

end BooleanAlgebra

end LeanMathlib
