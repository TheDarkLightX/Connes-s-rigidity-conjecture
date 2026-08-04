import LeanMathlib.Order.BooleanIntervalWitnessTransport
import Mathlib.Order.BooleanSubalgebra

namespace LeanMathlib

open scoped symmDiff

section BooleanSubalgebra

variable {α : Type*} [BooleanAlgebra α]
variable {L : BooleanSubalgebra α}

theorem subalg_disjoint_iff (p x y : L) :
    Disjoint p (x ⇔ y) ↔ Disjoint (p : α) (x ⇔ y) := by
  rw [disjoint_iff, disjoint_iff]
  constructor
  · intro h
    simpa using congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem subalg_codisjoint_iff (p x y : L) :
    Codisjoint p (x ∆ y) ↔ Codisjoint (p : α) (x ∆ y) := by
  rw [codisjoint_iff, codisjoint_iff]
  constructor
  · intro h
    simpa using congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem subalg_ne_iff_exists_atom_disjoint_bihimp [IsAtomic L] {x y : L} :
    x ≠ y ↔ ∃ p : L, IsAtom p ∧ Disjoint (p : α) (x ⇔ y) := by
  constructor
  · rintro hxy
    rcases (ne_iff_exists_atom_disjoint_bihimp (a := x) (b := y)).1 hxy with ⟨p, hp, hpd⟩
    exact ⟨p, hp, (subalg_disjoint_iff p x y).1 hpd⟩
  · rintro ⟨p, hp, hpd⟩
    exact (ne_iff_exists_atom_disjoint_bihimp (a := x) (b := y)).2
      ⟨p, hp, (subalg_disjoint_iff p x y).2 hpd⟩

theorem subalg_eq_iff_forall_atoms_not_disjoint_bihimp [IsAtomic L] {x y : L} :
    x = y ↔ ∀ p : L, IsAtom p → ¬ Disjoint (p : α) (x ⇔ y) := by
  constructor
  · intro h p hp hpd
    exact (eq_iff_forall_atom_not_disjoint_bihimp (a := x) (b := y)).1 h p hp
      ((subalg_disjoint_iff p x y).2 hpd)
  · intro h
    by_contra hxy
    rcases (ne_iff_exists_atom_disjoint_bihimp (a := x) (b := y)).1 hxy with ⟨p, hp, hpd⟩
    exact h p hp ((subalg_disjoint_iff p x y).1 hpd)

theorem subalg_ne_iff_exists_coatom_codisjoint_symmDiff [IsCoatomic L] {x y : L} :
    x ≠ y ↔ ∃ p : L, IsCoatom p ∧ Codisjoint (p : α) (x ∆ y) := by
  constructor
  · rintro hxy
    rcases (ne_iff_exists_coatom_codisjoint_symmDiff (a := x) (b := y)).1 hxy with
      ⟨p, hp, hpc⟩
    exact ⟨p, hp, (subalg_codisjoint_iff p x y).1 hpc⟩
  · rintro ⟨p, hp, hpc⟩
    exact (ne_iff_exists_coatom_codisjoint_symmDiff (a := x) (b := y)).2
      ⟨p, hp, (subalg_codisjoint_iff p x y).2 hpc⟩

theorem subalg_eq_iff_forall_coatoms_not_codisjoint_symmDiff [IsCoatomic L] {x y : L} :
    x = y ↔ ∀ p : L, IsCoatom p → ¬ Codisjoint (p : α) (x ∆ y) := by
  constructor
  · intro h p hp hpc
    exact (eq_iff_forall_coatom_not_codisjoint_symmDiff (a := x) (b := y)).1 h p hp
      ((subalg_codisjoint_iff p x y).2 hpc)
  · intro h
    by_contra hxy
    rcases (ne_iff_exists_coatom_codisjoint_symmDiff (a := x) (b := y)).1 hxy with
      ⟨p, hp, hpc⟩
    exact h p hp ((subalg_codisjoint_iff p x y).1 hpc)

end BooleanSubalgebra

end LeanMathlib
