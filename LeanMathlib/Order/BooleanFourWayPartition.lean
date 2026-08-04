import LeanMathlib.Order.AtomlessPartitionCertificates
import LeanMathlib.Order.BooleanWeakPartitionRefinement

namespace LeanMathlib

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

/-- Certificate that four Boolean pieces are nonzero, pairwise disjoint, and recompose `a`. -/
structure FourWayDecomposition (a w x y z : α) : Prop where
  first_nonzero : w ≠ ⊥
  second_nonzero : x ≠ ⊥
  third_nonzero : y ≠ ⊥
  fourth_nonzero : z ≠ ⊥
  first_second : Disjoint w x
  first_third : Disjoint w y
  first_fourth : Disjoint w z
  second_third : Disjoint x y
  second_fourth : Disjoint x z
  third_fourth : Disjoint y z
  sup_eq : ((w ⊔ x) ⊔ y) ⊔ z = a

namespace FourWayDecomposition

variable {a w x y z r : α}

theorem toWeak (h : FourWayDecomposition a w x y z) :
    WeakFourWayDecomposition a w x y z where
  first_second := h.first_second
  first_third := h.first_third
  first_fourth := h.first_fourth
  second_third := h.second_third
  second_fourth := h.second_fourth
  third_fourth := h.third_fourth
  sup_eq := h.sup_eq

theorem first_le_total (h : FourWayDecomposition a w x y z) : w ≤ a :=
  h.toWeak.toWeakTwoWayFirstRest.left_le_total

theorem fourth_le_total (h : FourWayDecomposition a w x y z) : z ≤ a :=
  h.toWeak.toWeakTwoWayLeft.right_le_total

theorem toThreeWayLeftPair (h : FourWayDecomposition a w x y z) :
    ThreeWayDecomposition a (w ⊔ x) y z where
  first_nonzero := sup_ne_bot_of_left_ne_bot h.first_nonzero
  second_nonzero := h.third_nonzero
  third_nonzero := h.fourth_nonzero
  first_second := h.first_third.sup_left h.second_third
  first_third := h.first_fourth.sup_left h.second_fourth
  second_third := h.third_fourth
  sup_eq := h.sup_eq

theorem toThreeWayMiddlePair (h : FourWayDecomposition a w x y z) :
    ThreeWayDecomposition a w (x ⊔ y) z where
  first_nonzero := h.first_nonzero
  second_nonzero := sup_ne_bot_of_left_ne_bot h.second_nonzero
  third_nonzero := h.fourth_nonzero
  first_second := h.first_second.sup_right h.first_third
  first_third := h.first_fourth
  second_third := h.second_fourth.sup_left h.third_fourth
  sup_eq := by
    calc
      (w ⊔ (x ⊔ y)) ⊔ z = ((w ⊔ x) ⊔ y) ⊔ z := by ac_rfl
      _ = a := h.sup_eq

theorem toThreeWayRightPair (h : FourWayDecomposition a w x y z) :
    ThreeWayDecomposition a w x (y ⊔ z) where
  first_nonzero := h.first_nonzero
  second_nonzero := h.second_nonzero
  third_nonzero := sup_ne_bot_of_left_ne_bot h.third_nonzero
  first_second := h.first_second
  first_third := h.first_third.sup_right h.first_fourth
  second_third := h.second_third.sup_right h.second_fourth
  sup_eq := by
    calc
      (w ⊔ x) ⊔ (y ⊔ z) = ((w ⊔ x) ⊔ y) ⊔ z := by ac_rfl
      _ = a := h.sup_eq

theorem toTwoWayPairPair (h : FourWayDecomposition a w x y z) :
    TwoWayDecomposition a (w ⊔ x) (y ⊔ z) where
  left_nonzero := sup_ne_bot_of_left_ne_bot h.first_nonzero
  right_nonzero := sup_ne_bot_of_left_ne_bot h.third_nonzero
  disjoint := h.toWeak.toWeakTwoWayPairPair.disjoint
  sup_eq := h.toWeak.toWeakTwoWayPairPair.sup_eq

theorem ofNestedRight
    (outer : ThreeWayDecomposition a w x r) (inner : TwoWayDecomposition r y z) :
    FourWayDecomposition a w x y z where
  first_nonzero := outer.first_nonzero
  second_nonzero := outer.second_nonzero
  third_nonzero := inner.left_nonzero
  fourth_nonzero := inner.right_nonzero
  first_second := outer.first_second
  first_third := outer.first_third.mono_right inner.left_le_total
  first_fourth := outer.first_third.mono_right inner.right_le_total
  second_third := outer.second_third.mono_right inner.left_le_total
  second_fourth := outer.second_third.mono_right inner.right_le_total
  third_fourth := inner.disjoint
  sup_eq := by
    calc
      ((w ⊔ x) ⊔ y) ⊔ z = (w ⊔ x) ⊔ (y ⊔ z) := by rw [sup_assoc]
      _ = (w ⊔ x) ⊔ r := by rw [inner.sup_eq]
      _ = a := outer.sup_eq

end FourWayDecomposition

end BooleanAlgebra

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/-- Every nonzero element of an atomless Boolean algebra has a strong four-way partition. -/
theorem exists_fourWayDecomposition {a : α} (ha : a ≠ ⊥) :
    ∃ w x y z : α, FourWayDecomposition a w x y z := by
  obtain ⟨w, x, r, houter⟩ := exists_threeWayDecomposition (α := α) ha
  obtain ⟨y, z, hinner⟩ := exists_twoWayDecomposition (α := α) houter.third_nonzero
  exact ⟨w, x, y, z, FourWayDecomposition.ofNestedRight houter hinner⟩

end Atomless

end LeanMathlib
