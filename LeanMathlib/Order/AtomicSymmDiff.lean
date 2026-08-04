import LeanMathlib.Order.AtomicBooleanAlgebra
import LeanMathlib.Order.SymmDiffDecomposition

namespace LeanMathlib

open scoped symmDiff

section Atomic

variable {α : Type*} [BooleanAlgebra α] [IsAtomic α]

omit [IsAtomic α] in
theorem atom_le_symmDiff_of_le_left {a b p : α} (hpa : p ≤ a) (hdisj : Disjoint p b) :
    p ≤ a ∆ b := by
  rw [symmDiff_eq_rightSplit_sup_rightSplit]
  exact le_sup_of_le_left ((le_sdiff).2 ⟨hpa, hdisj⟩)

omit [IsAtomic α] in
theorem atom_le_symmDiff_of_le_right {a b p : α} (hpb : p ≤ b) (hdisj : Disjoint p a) :
    p ≤ a ∆ b := by
  rw [symmDiff_eq_rightSplit_sup_rightSplit]
  exact le_sup_of_le_right ((le_sdiff).2 ⟨hpb, hdisj⟩)

theorem ne_iff_exists_atom_witness {a b : α} :
    a ≠ b ↔
      (∃ p : α, IsAtom p ∧ p ≤ a ∧ Disjoint p b) ∨
      (∃ p : α, IsAtom p ∧ p ≤ b ∧ Disjoint p a) := by
  refine ⟨fun hne => ?_, fun h => ?_⟩
  · by_cases hab : a ≤ b
    · right
      have hba : ¬ b ≤ a := by
        intro hba
        exact hne (le_antisymm hab hba)
      exact (not_le_iff_exists_atom_disjoint (a := b) (b := a)).1 hba
    · left
      exact (not_le_iff_exists_atom_disjoint (a := a) (b := b)).1 hab
  · intro hab
    rcases h with h | h
    · rcases h with ⟨p, hp, hpa, hdisj⟩
      exact ((hp.not_le_iff_disjoint).2 (hab ▸ hdisj)) hpa
    · rcases h with ⟨p, hp, hpb, hdisj⟩
      exact ((hp.not_le_iff_disjoint).2 (hab ▸ hdisj)) hpb

theorem ne_iff_exists_atom_le_symmDiff {a b : α} :
    a ≠ b ↔ ∃ p : α, IsAtom p ∧ p ≤ a ∆ b := by
  refine ⟨fun hne => ?_, fun h hab => ?_⟩
  · rcases (ne_iff_exists_atom_witness (a := a) (b := b)).1 hne with h | h
    · rcases h with ⟨p, hp, hpa, hdisj⟩
      exact ⟨p, hp, atom_le_symmDiff_of_le_left hpa hdisj⟩
    · rcases h with ⟨p, hp, hpb, hdisj⟩
      exact ⟨p, hp, atom_le_symmDiff_of_le_right hpb hdisj⟩
  · rcases h with ⟨p, hp, hpdiff⟩
    have hbot : p ≤ (⊥ : α) := by simpa [hab] using hpdiff
    exact hp.ne_bot (le_bot_iff.mp hbot)

theorem eq_iff_forall_atom_not_le_symmDiff {a b : α} :
    a = b ↔ ∀ p : α, IsAtom p → ¬ p ≤ a ∆ b := by
  refine ⟨fun hab p hp => ?_, fun h => ?_⟩
  · have hbot : ¬ p ≤ (⊥ : α) := by
      intro hpbot
      exact hp.ne_bot (le_bot_iff.mp hpbot)
    simpa [hab] using hbot
  · by_contra hne
    rcases (ne_iff_exists_atom_le_symmDiff (a := a) (b := b)).1 hne with ⟨p, hp, hple⟩
    exact (h p hp) hple

end Atomic

end LeanMathlib
