import LeanMathlib.Order.BooleanPartition
import LeanMathlib.Order.AtomlessPartitionRefinement
import LeanMathlib.Order.AtomlessThreeWaySplit

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/-- Every nonzero element of an atomless Boolean algebra has a two-way partition certificate. -/
theorem exists_twoWayDecomposition {a : α} (ha : a ≠ ⊥) :
    ∃ x y : α, TwoWayDecomposition a x y := by
  obtain ⟨x, y, hx0, hy0, hxy, hsup⟩ := exists_nontrivial_split ha
  exact ⟨x, y, ⟨hx0, hy0, hxy, hsup⟩⟩

/-- Every nonzero element of an atomless Boolean algebra has a three-way partition certificate. -/
theorem exists_threeWayDecomposition {a : α} (ha : a ≠ ⊥) :
    ∃ x y z : α, ThreeWayDecomposition a x y z := by
  obtain ⟨x, y, z, hx0, hy0, hz0, hxy, hxz, hyz, hsup⟩ := exists_threeway_split ha
  exact ⟨x, y, z, ⟨hx0, hy0, hz0, hxy, hxz, hyz, hsup⟩⟩

/--
In an atomless Boolean algebra, the left side of a two-way partition certificate
can be refined into a three-way certificate without changing the total.
-/
theorem TwoWayDecomposition.exists_refine_left
    {a x y : α} (h : TwoWayDecomposition a x y) :
    ∃ u v : α, ThreeWayDecomposition a u v y := by
  obtain ⟨u, v, hu0, hv0, huv, huy, hvy, huv_sup⟩ :=
    exists_split_preserving_disjoint_right h.left_nonzero h.disjoint
  refine ⟨u, v, ?_⟩
  exact
    { first_nonzero := hu0
      second_nonzero := hv0
      third_nonzero := h.right_nonzero
      first_second := huv
      first_third := huy
      second_third := hvy
      sup_eq := by
        calc
          (u ⊔ v) ⊔ y = x ⊔ y := by rw [huv_sup]
          _ = a := h.sup_eq }

/--
In an atomless Boolean algebra, the right side of a two-way partition certificate
can be refined into a three-way certificate without changing the total.
-/
theorem TwoWayDecomposition.exists_refine_right
    {a x y : α} (h : TwoWayDecomposition a x y) :
    ∃ u v : α, ThreeWayDecomposition a x u v := by
  obtain ⟨u, v, hu0, hv0, huv, hxu, hxv, huv_sup⟩ :=
    exists_split_preserving_disjoint_left h.right_nonzero h.disjoint
  refine ⟨u, v, ?_⟩
  exact
    { first_nonzero := h.left_nonzero
      second_nonzero := hu0
      third_nonzero := hv0
      first_second := hxu
      first_third := hxv
      second_third := huv
      sup_eq := by
        calc
          (x ⊔ u) ⊔ v = x ⊔ (u ⊔ v) := by rw [sup_assoc]
          _ = x ⊔ y := by rw [huv_sup]
          _ = a := h.sup_eq }

end Atomless

end LeanMathlib
