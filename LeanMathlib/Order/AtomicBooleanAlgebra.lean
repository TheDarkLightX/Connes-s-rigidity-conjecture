import LeanMathlib.Order.BooleanDecomposition
import Mathlib.Order.Atoms

namespace LeanMathlib

section Atomic

variable {α : Type*} [BooleanAlgebra α]

theorem exists_atom_le_of_ne_bot [IsAtomic α] {a : α} (ha : a ≠ ⊥) :
    ∃ p : α, IsAtom p ∧ p ≤ a := by
  exact (eq_bot_or_exists_atom_le a).resolve_left ha

theorem atom_leftSplit_eq_bot_or_self {a p : α} (hp : IsAtom p) :
    leftSplit p a = ⊥ ∨ leftSplit p a = p := by
  exact hp.le_iff.mp (leftSplit_le_left p a)

theorem atom_inf_eq_bot_or_eq_self {a p : α} (hp : IsAtom p) :
    p ⊓ a = ⊥ ∨ p ⊓ a = p := by
  simpa [leftSplit] using atom_leftSplit_eq_bot_or_self (a := a) hp

theorem atom_rightSplit_eq_bot_or_self {a p : α} (hp : IsAtom p) :
    rightSplit p a = ⊥ ∨ rightSplit p a = p := by
  exact hp.le_iff.mp (rightSplit_le_left p a)

theorem atom_rightSplit_eq_self_iff {a p : α} :
    rightSplit p a = p ↔ Disjoint p a := by
  simp [rightSplit]

theorem atom_le_or_disjoint {a p : α} (hp : IsAtom p) :
    p ≤ a ∨ Disjoint p a := by
  by_cases h : p ≤ a
  · exact Or.inl h
  · exact Or.inr ((hp.not_le_iff_disjoint).1 h)

theorem atom_le_or_le_compl {a p : α} (hp : IsAtom p) :
    p ≤ a ∨ p ≤ aᶜ := by
  obtain h | h := atom_le_or_disjoint (a := a) hp
  · exact Or.inl h
  · exact Or.inr ((le_compl_iff_disjoint_right).2 h)

theorem exists_atom_rightSplit_of_ne_bot [IsAtomic α] {a b : α}
    (h : rightSplit a b ≠ ⊥) :
    ∃ p : α, IsAtom p ∧ p ≤ a ∧ Disjoint p b := by
  obtain ⟨p, hp, hple⟩ := exists_atom_le_of_ne_bot (a := rightSplit a b) h
  have hdisj : Disjoint (rightSplit a b) b := by
    simpa [rightSplit] using (disjoint_sdiff_self_left : Disjoint (a \ b) b)
  refine ⟨p, hp, hple.trans (rightSplit_le_left a b), hdisj.mono_left hple⟩

theorem not_le_iff_exists_atom_disjoint [IsAtomic α] {a b : α} :
    ¬ a ≤ b ↔ ∃ p : α, IsAtom p ∧ p ≤ a ∧ Disjoint p b := by
  refine ⟨fun h => ?_, fun h hab => ?_⟩
  · exact exists_atom_rightSplit_of_ne_bot ((rightSplit_ne_bot_iff a b).2 h)
  · rcases h with ⟨p, hp, hpa, hdisj⟩
    exact ((hp.not_le_iff_disjoint).2 hdisj) (hpa.trans hab)

end Atomic

end LeanMathlib
