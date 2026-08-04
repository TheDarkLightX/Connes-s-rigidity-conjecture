import LeanMathlib.Order.BooleanLowerIntervalTransport
import Mathlib.Order.Hom.Set
import Mathlib.Order.ModularLattice

namespace LeanMathlib

namespace OrderIso

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem isAtomless (f : α ≃o β) [IsAtomless α] : IsAtomless β := by
  refine ⟨fun {b} hb => ?_⟩
  have hpre : f.symm b ≠ ⊥ := by
    intro hs
    apply hb
    rw [← f.map_bot, ← hs, f.apply_symm_apply]
  obtain ⟨a, ha0, ha_lt⟩ := exists_lt_nonzero (α := α) (a := f.symm b) hpre
  refine ⟨f a, ?_, ?_⟩
  · intro hfa
    apply ha0
    apply f.injective
    rw [hfa, f.map_bot]
  · simpa using f.strictMono ha_lt

theorem isAtomless_iff (f : α ≃o β) : IsAtomless α ↔ IsAtomless β := by
  constructor
  · intro h
    let _ : IsAtomless α := h
    exact LeanMathlib.OrderIso.isAtomless f
  · intro h
    let _ : IsAtomless β := h
    exact LeanMathlib.OrderIso.isAtomless f.symm

end OrderIso

@[simp]
theorem isAtomless_dual_iff {α : Type*} [BooleanAlgebra α] :
    IsAtomless αᵒᵈ ↔ IsAtomless α := by
  simpa using (LeanMathlib.OrderIso.isAtomless_iff (OrderIso.compl α)).symm

namespace IsCompl

variable {α : Type*} [BooleanAlgebra α] {a b : α}

theorem iic_isAtomless_iff_ici_isAtomless (h : IsCompl a b) :
    IsAtomless (Set.Iic a) ↔ IsAtomless (Set.Ici b) := by
  simpa using LeanMathlib.OrderIso.isAtomless_iff h.IicOrderIsoIci

theorem iic_isAtomic_iff_ici_isAtomic (h : IsCompl a b) :
    IsAtomic (Set.Iic a) ↔ IsAtomic (Set.Ici b) := by
  simpa using (h.IicOrderIsoIci).isAtomic_iff

theorem iic_isCoatomic_iff_ici_isCoatomic (h : IsCompl a b) :
    IsCoatomic (Set.Iic a) ↔ IsCoatomic (Set.Ici b) := by
  simpa using (h.IicOrderIsoIci).isCoatomic_iff

end IsCompl

end LeanMathlib
