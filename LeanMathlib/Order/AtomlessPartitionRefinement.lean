import LeanMathlib.Order.AtomlessBooleanAlgebra

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/--
Refine one nonzero part of a disjoint Boolean decomposition while preserving
disjointness from the untouched remainder.
-/
theorem exists_split_preserving_disjoint_right {a r : α}
    (ha : a ≠ ⊥) (har : Disjoint a r) :
    ∃ x y : α,
      x ≠ ⊥ ∧ y ≠ ⊥ ∧
      Disjoint x y ∧ Disjoint x r ∧ Disjoint y r ∧ x ⊔ y = a := by
  obtain ⟨x, y, hx0, hy0, hxy, hxy_sup⟩ := exists_nontrivial_split ha
  have hx_le_a : x ≤ a := by
    rw [← hxy_sup]
    exact le_sup_left
  have hy_le_a : y ≤ a := by
    rw [← hxy_sup]
    exact le_sup_right
  exact ⟨x, y, hx0, hy0, hxy, har.mono_left hx_le_a, har.mono_left hy_le_a, hxy_sup⟩

theorem exists_split_preserving_disjoint_left {r a : α}
    (ha : a ≠ ⊥) (hra : Disjoint r a) :
    ∃ x y : α,
      x ≠ ⊥ ∧ y ≠ ⊥ ∧
      Disjoint x y ∧ Disjoint r x ∧ Disjoint r y ∧ x ⊔ y = a := by
  obtain ⟨x, y, hx0, hy0, hxy, hxr, hyr, hxy_sup⟩ :=
    exists_split_preserving_disjoint_right ha hra.symm
  exact ⟨x, y, hx0, hy0, hxy, hxr.symm, hyr.symm, hxy_sup⟩

/--
Refining one nonzero part of a two-piece decomposition preserves the total
join and all pairwise disjointness obligations.
-/
theorem exists_split_refinement_recompose {a r p : α}
    (ha : a ≠ ⊥) (har : Disjoint a r) (hp : a ⊔ r = p) :
    ∃ x y : α,
      x ≠ ⊥ ∧ y ≠ ⊥ ∧
      Disjoint x y ∧ Disjoint x r ∧ Disjoint y r ∧ (x ⊔ y) ⊔ r = p := by
  obtain ⟨x, y, hx0, hy0, hxy, hxr, hyr, hxy_sup⟩ :=
    exists_split_preserving_disjoint_right ha har
  refine ⟨x, y, hx0, hy0, hxy, hxr, hyr, ?_⟩
  rw [hxy_sup, hp]

end Atomless

end LeanMathlib
