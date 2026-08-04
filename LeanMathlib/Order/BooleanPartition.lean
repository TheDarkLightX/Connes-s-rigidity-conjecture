import LeanMathlib.Order.BooleanDecomposition

namespace LeanMathlib

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

/-- Certificate that `x` and `y` are nonzero disjoint pieces recomposing `a`. -/
structure TwoWayDecomposition (a x y : α) : Prop where
  left_nonzero : x ≠ ⊥
  right_nonzero : y ≠ ⊥
  disjoint : Disjoint x y
  sup_eq : x ⊔ y = a

/-- Certificate that `x`, `y`, and `z` are nonzero pairwise-disjoint pieces recomposing `a`. -/
structure ThreeWayDecomposition (a x y z : α) : Prop where
  first_nonzero : x ≠ ⊥
  second_nonzero : y ≠ ⊥
  third_nonzero : z ≠ ⊥
  first_second : Disjoint x y
  first_third : Disjoint x z
  second_third : Disjoint y z
  sup_eq : (x ⊔ y) ⊔ z = a

theorem sup_ne_bot_of_left_ne_bot {x y : α} (hx : x ≠ ⊥) : x ⊔ y ≠ ⊥ := by
  intro hsup
  have hx_le_bot : x ≤ (⊥ : α) := le_trans le_sup_left (le_of_eq hsup)
  exact hx (le_bot_iff.mp hx_le_bot)

namespace TwoWayDecomposition

variable {a x y z r : α}

theorem symm (h : TwoWayDecomposition a x y) : TwoWayDecomposition a y x where
  left_nonzero := h.right_nonzero
  right_nonzero := h.left_nonzero
  disjoint := h.disjoint.symm
  sup_eq := by
    rw [sup_comm, h.sup_eq]

theorem left_le_total (h : TwoWayDecomposition a x y) : x ≤ a := by
  rw [← h.sup_eq]
  exact le_sup_left

theorem right_le_total (h : TwoWayDecomposition a x y) : y ≤ a := by
  rw [← h.sup_eq]
  exact le_sup_right

theorem disjoint_symm (h : TwoWayDecomposition a x y) : Disjoint y x :=
  h.disjoint.symm

theorem rightSplit_ne_bot_of_lt {a b : α} (hba : b < a) :
    rightSplit a b ≠ ⊥ := by
  intro hsplit
  have hab : a ≤ b := (rightSplit_eq_bot_iff a b).1 hsplit
  exact hba.ne (le_antisymm hba.le hab)

theorem of_rightSplit {a b : α} (hb0 : b ≠ ⊥) (hba : b < a) :
    TwoWayDecomposition a b (rightSplit a b) where
  left_nonzero := hb0
  right_nonzero := rightSplit_ne_bot_of_lt hba
  disjoint := by
    have hdisj : Disjoint (leftSplit a b) (rightSplit a b) :=
      leftSplit_disjoint_rightSplit a b
    simpa [leftSplit_eq_right_of_le a b hba.le] using hdisj
  sup_eq := split_recompose_of_le a b hba.le

end TwoWayDecomposition

namespace ThreeWayDecomposition

variable {a x y z r : α}

theorem first_le_total (h : ThreeWayDecomposition a x y z) : x ≤ a := by
  rw [← h.sup_eq]
  exact le_trans le_sup_left le_sup_left

theorem second_le_total (h : ThreeWayDecomposition a x y z) : y ≤ a := by
  rw [← h.sup_eq]
  exact le_trans le_sup_right le_sup_left

theorem third_le_total (h : ThreeWayDecomposition a x y z) : z ≤ a := by
  rw [← h.sup_eq]
  exact le_sup_right

theorem toTwoWayLeft (h : ThreeWayDecomposition a x y z) :
    TwoWayDecomposition a (x ⊔ y) z where
  left_nonzero := sup_ne_bot_of_left_ne_bot h.first_nonzero
  right_nonzero := h.third_nonzero
  disjoint := h.first_third.sup_left h.second_third
  sup_eq := h.sup_eq

theorem toTwoWayRight (h : ThreeWayDecomposition a x y z) :
    TwoWayDecomposition a x (y ⊔ z) where
  left_nonzero := h.first_nonzero
  right_nonzero := sup_ne_bot_of_left_ne_bot h.second_nonzero
  disjoint := h.first_second.sup_right h.first_third
  sup_eq := by
    calc
      x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by rw [sup_assoc]
      _ = a := h.sup_eq

theorem ofNested
    (outer : TwoWayDecomposition a x r) (inner : TwoWayDecomposition r y z) :
    ThreeWayDecomposition a x y z where
  first_nonzero := outer.left_nonzero
  second_nonzero := inner.left_nonzero
  third_nonzero := inner.right_nonzero
  first_second := outer.disjoint.mono_right inner.left_le_total
  first_third := outer.disjoint.mono_right inner.right_le_total
  second_third := inner.disjoint
  sup_eq := by
    calc
      (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) := by rw [sup_assoc]
      _ = x ⊔ r := by rw [inner.sup_eq]
      _ = a := outer.sup_eq

end ThreeWayDecomposition

end BooleanAlgebra

end LeanMathlib
