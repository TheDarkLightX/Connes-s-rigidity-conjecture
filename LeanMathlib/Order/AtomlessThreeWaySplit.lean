import LeanMathlib.Order.AtomlessBooleanAlgebra

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/--
Every nonzero element of an atomless Boolean algebra can be refined into three
nonzero pairwise-disjoint pieces.
-/
theorem exists_threeway_split {a : α} (ha : a ≠ ⊥) :
    ∃ x y z : α,
      x ≠ ⊥ ∧ y ≠ ⊥ ∧ z ≠ ⊥ ∧
      Disjoint x y ∧ Disjoint x z ∧ Disjoint y z ∧ (x ⊔ y) ⊔ z = a := by
  obtain ⟨x, r, hx0, hr0, hxr, hxr_sup⟩ := exists_nontrivial_split ha
  obtain ⟨y, z, hy0, hz0, hyz, hyz_sup⟩ := exists_nontrivial_split hr0
  have hy_le_r : y ≤ r := by
    rw [← hyz_sup]
    exact le_sup_left
  have hz_le_r : z ≤ r := by
    rw [← hyz_sup]
    exact le_sup_right
  refine ⟨x, y, z, hx0, hy0, hz0, ?_, ?_, hyz, ?_⟩
  · exact hxr.mono_right hy_le_r
  · exact hxr.mono_right hz_le_r
  · calc
      (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) := by rw [sup_assoc]
      _ = x ⊔ r := by rw [hyz_sup]
      _ = a := hxr_sup

end Atomless

end LeanMathlib
