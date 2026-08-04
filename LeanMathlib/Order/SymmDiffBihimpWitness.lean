import LeanMathlib.Order.CoatomicBihimp

namespace LeanMathlib

open scoped symmDiff

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

theorem le_symmDiff_iff_disjoint_bihimp {a b p : α} :
    p ≤ a ∆ b ↔ Disjoint p (a ⇔ b) := by
  rw [← le_compl_iff_disjoint_right, compl_bihimp]

theorem bihimp_le_iff_codisjoint_symmDiff {a b p : α} :
    a ⇔ b ≤ p ↔ Codisjoint p (a ∆ b) := by
  rw [codisjoint_iff_compl_le_left, compl_symmDiff]

theorem isCompl_symmDiff_bihimp (a b : α) : IsCompl (a ∆ b) (a ⇔ b) := by
  constructor
  · rw [disjoint_iff]
    simpa [compl_symmDiff] using (inf_compl_eq_bot (a := a ∆ b))
  · rw [codisjoint_iff]
    simpa [compl_symmDiff] using (sup_compl_eq_top (x := a ∆ b))

end BooleanAlgebra

section Atomic

variable {α : Type*} [BooleanAlgebra α] [IsAtomic α]

theorem ne_iff_exists_atom_disjoint_bihimp {a b : α} :
    a ≠ b ↔ ∃ p : α, IsAtom p ∧ Disjoint p (a ⇔ b) := by
  simpa [le_symmDiff_iff_disjoint_bihimp] using
    (ne_iff_exists_atom_le_symmDiff (a := a) (b := b))

theorem eq_iff_forall_atom_not_disjoint_bihimp {a b : α} :
    a = b ↔ ∀ p : α, IsAtom p → ¬ Disjoint p (a ⇔ b) := by
  simpa [le_symmDiff_iff_disjoint_bihimp] using
    (eq_iff_forall_atom_not_le_symmDiff (a := a) (b := b))

end Atomic

section Coatomic

variable {α : Type*} [BooleanAlgebra α] [IsCoatomic α]

theorem ne_iff_exists_coatom_codisjoint_symmDiff {a b : α} :
    a ≠ b ↔ ∃ p : α, IsCoatom p ∧ Codisjoint p (a ∆ b) := by
  simpa [bihimp_le_iff_codisjoint_symmDiff] using
    (ne_iff_exists_coatom_ge_bihimp (a := a) (b := b))

theorem eq_iff_forall_coatom_not_codisjoint_symmDiff {a b : α} :
    a = b ↔ ∀ p : α, IsCoatom p → ¬ Codisjoint p (a ∆ b) := by
  simpa [bihimp_le_iff_codisjoint_symmDiff] using
    (eq_iff_forall_coatom_not_ge_bihimp (a := a) (b := b))

end Coatomic

end LeanMathlib
