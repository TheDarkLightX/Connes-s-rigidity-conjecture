import LeanMathlib.Order.BooleanSubalgebraMapTransport

namespace LeanMathlib

namespace BooleanSubalgebra

open scoped symmDiff

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem equivMap_ne_iff_exists_atom_disjoint_bihimp (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) (L : BooleanSubalgebra α) [IsAtomic L] {x y : L} :
    x ≠ y ↔
      ∃ p : L.map f, IsAtom p ∧
        Disjoint (p : β) ((equivMap f hf L x : L.map f) ⇔ equivMap f hf L y) := by
  let _ : IsAtomic (L.map f) := (isAtomic_iff_equivMap (f := f) (hf := hf) (L := L)).2 inferInstance
  simpa using
    (subalg_ne_iff_exists_atom_disjoint_bihimp (L := L.map f)
      (x := equivMap f hf L x) (y := equivMap f hf L y))

theorem equivMap_eq_iff_forall_atoms_not_disjoint_bihimp (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) (L : BooleanSubalgebra α) [IsAtomic L] {x y : L} :
    x = y ↔
      ∀ p : L.map f, IsAtom p →
        ¬ Disjoint (p : β) ((equivMap f hf L x : L.map f) ⇔ equivMap f hf L y) := by
  let _ : IsAtomic (L.map f) := (isAtomic_iff_equivMap (f := f) (hf := hf) (L := L)).2 inferInstance
  simpa using
    (subalg_eq_iff_forall_atoms_not_disjoint_bihimp (L := L.map f)
      (x := equivMap f hf L x) (y := equivMap f hf L y))

theorem equivMap_ne_iff_exists_coatom_codisjoint_symmDiff (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) (L : BooleanSubalgebra α) [IsCoatomic L] {x y : L} :
    x ≠ y ↔
      ∃ p : L.map f, IsCoatom p ∧
        Codisjoint (p : β) ((equivMap f hf L x : L.map f) ∆ equivMap f hf L y) := by
  let _ : IsCoatomic (L.map f) :=
    (isCoatomic_iff_equivMap (f := f) (hf := hf) (L := L)).2 inferInstance
  simpa using
    (subalg_ne_iff_exists_coatom_codisjoint_symmDiff (L := L.map f)
      (x := equivMap f hf L x) (y := equivMap f hf L y))

theorem equivMap_eq_iff_forall_coatoms_not_codisjoint_symmDiff (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) (L : BooleanSubalgebra α) [IsCoatomic L] {x y : L} :
    x = y ↔
      ∀ p : L.map f, IsCoatom p →
        ¬ Codisjoint (p : β) ((equivMap f hf L x : L.map f) ∆ equivMap f hf L y) := by
  let _ : IsCoatomic (L.map f) :=
    (isCoatomic_iff_equivMap (f := f) (hf := hf) (L := L)).2 inferInstance
  simpa using
    (subalg_eq_iff_forall_coatoms_not_codisjoint_symmDiff (L := L.map f)
      (x := equivMap f hf L x) (y := equivMap f hf L y))

end BooleanAlgebra

end BooleanSubalgebra

end LeanMathlib
