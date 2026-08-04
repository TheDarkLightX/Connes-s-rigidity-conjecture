import LeanMathlib.Order.BooleanFourWayPartition

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]
variable {a x y z : α}

theorem ThreeWayDecomposition.exists_refine_first_to_fourWay
    (h : ThreeWayDecomposition a x y z) :
    ∃ u v : α, FourWayDecomposition a u v y z := by
  obtain ⟨u, v, hu0, hv0, huv, huv_sup⟩ := exists_nontrivial_split h.first_nonzero
  have hu_le_x : u ≤ x := by
    rw [← huv_sup]
    exact le_sup_left
  have hv_le_x : v ≤ x := by
    rw [← huv_sup]
    exact le_sup_right
  refine ⟨u, v, ?_⟩
  exact
    { first_nonzero := hu0
      second_nonzero := hv0
      third_nonzero := h.second_nonzero
      fourth_nonzero := h.third_nonzero
      first_second := huv
      first_third := h.first_second.mono_left hu_le_x
      first_fourth := h.first_third.mono_left hu_le_x
      second_third := h.first_second.mono_left hv_le_x
      second_fourth := h.first_third.mono_left hv_le_x
      third_fourth := h.second_third
      sup_eq := by
        calc
          ((u ⊔ v) ⊔ y) ⊔ z = (x ⊔ y) ⊔ z := by rw [huv_sup]
          _ = a := h.sup_eq }

theorem ThreeWayDecomposition.exists_refine_second_to_fourWay
    (h : ThreeWayDecomposition a x y z) :
    ∃ u v : α, FourWayDecomposition a x u v z := by
  obtain ⟨u, v, hu0, hv0, huv, huv_sup⟩ := exists_nontrivial_split h.second_nonzero
  have hu_le_y : u ≤ y := by
    rw [← huv_sup]
    exact le_sup_left
  have hv_le_y : v ≤ y := by
    rw [← huv_sup]
    exact le_sup_right
  refine ⟨u, v, ?_⟩
  exact
    { first_nonzero := h.first_nonzero
      second_nonzero := hu0
      third_nonzero := hv0
      fourth_nonzero := h.third_nonzero
      first_second := h.first_second.mono_right hu_le_y
      first_third := h.first_second.mono_right hv_le_y
      first_fourth := h.first_third
      second_third := huv
      second_fourth := h.second_third.mono_left hu_le_y
      third_fourth := h.second_third.mono_left hv_le_y
      sup_eq := by
        calc
          ((x ⊔ u) ⊔ v) ⊔ z = (x ⊔ (u ⊔ v)) ⊔ z := by ac_rfl
          _ = (x ⊔ y) ⊔ z := by rw [huv_sup]
          _ = a := h.sup_eq }

theorem ThreeWayDecomposition.exists_refine_third_to_fourWay
    (h : ThreeWayDecomposition a x y z) :
    ∃ u v : α, FourWayDecomposition a x y u v := by
  obtain ⟨u, v, inner⟩ := exists_twoWayDecomposition (α := α) h.third_nonzero
  exact ⟨u, v, FourWayDecomposition.ofNestedRight h inner⟩

end Atomless

end LeanMathlib
