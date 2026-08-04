import LeanMathlib.Order.AtomlessOrderDensity
import Mathlib.Order.Cover

namespace LeanMathlib

section Atomless

variable (α : Type*) [BooleanAlgebra α] [IsAtomless α]

/-- The local atomless Boolean algebra property supplies mathlib's dense-order class. -/
instance instDenselyOrderedOfIsAtomless : DenselyOrdered α where
  dense := by
    intro a b hab
    exact exists_between_of_lt hab

end Atomless

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

theorem not_covBy_of_isAtomless (a b : α) : ¬ a ⋖ b := by
  let _ : DenselyOrdered α := instDenselyOrderedOfIsAtomless α
  exact not_covBy

theorem not_wCovBy_of_lt {a b : α} (hab : a < b) : ¬ a ⩿ b := by
  intro hcov
  exact not_covBy_of_isAtomless a b ⟨hab, hcov.2⟩

theorem not_isCoatom (a : α) : ¬ IsCoatom a := by
  intro ha
  exact not_covBy_of_isAtomless a ⊤ ha.covBy_top

theorem not_isCoatomic [Nontrivial α] : ¬ IsCoatomic α := by
  intro hCoatomic
  let _ : IsCoatomic α := hCoatomic
  obtain ⟨a, ha⟩ := IsCoatomic.exists_coatom (α := α)
  exact not_isCoatom a ha

theorem not_isStronglyAtomic [Nontrivial α] : ¬ IsStronglyAtomic α := by
  intro hStrong
  let _ : IsStronglyAtomic α := hStrong
  have hbot_top : (⊥ : α) < ⊤ := lt_of_le_of_ne bot_le bot_ne_top
  obtain ⟨x, hx_cov, _hx_top⟩ := exists_covBy_le_of_lt hbot_top
  exact not_covBy_of_isAtomless ⊥ x hx_cov

theorem not_isStronglyCoatomic [Nontrivial α] : ¬ IsStronglyCoatomic α := by
  intro hStrong
  let _ : IsStronglyCoatomic α := hStrong
  have hbot_top : (⊥ : α) < ⊤ := lt_of_le_of_ne bot_le bot_ne_top
  obtain ⟨x, _hbot_x, hx_cov⟩ := exists_le_covBy_of_lt hbot_top
  exact not_covBy_of_isAtomless x ⊤ hx_cov

end Atomless

end LeanMathlib
