import LeanMathlib.Order.AtomicSymmDiff

namespace LeanMathlib

open scoped symmDiff

section Coatomic

variable {α : Type*} [BooleanAlgebra α] [IsCoatomic α]

omit [IsCoatomic α] in
theorem coatom_ge_bihimp_of_le_left {a b p : α} (hap : a ≤ p) (hcodisj : Codisjoint p b) :
    a ⇔ b ≤ p := by
  simpa using
    (atom_le_symmDiff_of_le_left (α := αᵒᵈ) (a := a) (b := b) (p := p) hap hcodisj)

omit [IsCoatomic α] in
theorem coatom_ge_bihimp_of_le_right {a b p : α} (hbp : b ≤ p) (hcodisj : Codisjoint p a) :
    a ⇔ b ≤ p := by
  simpa using
    (atom_le_symmDiff_of_le_right (α := αᵒᵈ) (a := a) (b := b) (p := p) hbp hcodisj)

theorem ne_iff_exists_coatom_witness {a b : α} :
    a ≠ b ↔
      (∃ p : α, IsCoatom p ∧ a ≤ p ∧ Codisjoint p b) ∨
      (∃ p : α, IsCoatom p ∧ b ≤ p ∧ Codisjoint p a) := by
  simpa using (ne_iff_exists_atom_witness (α := αᵒᵈ) (a := a) (b := b))

theorem ne_iff_exists_coatom_ge_bihimp {a b : α} :
    a ≠ b ↔ ∃ p : α, IsCoatom p ∧ a ⇔ b ≤ p := by
  simpa using (ne_iff_exists_atom_le_symmDiff (α := αᵒᵈ) (a := a) (b := b))

theorem eq_iff_forall_coatom_not_ge_bihimp {a b : α} :
    a = b ↔ ∀ p : α, IsCoatom p → ¬ a ⇔ b ≤ p := by
  simpa using (eq_iff_forall_atom_not_le_symmDiff (α := αᵒᵈ) (a := a) (b := b))

end Coatomic

end LeanMathlib
