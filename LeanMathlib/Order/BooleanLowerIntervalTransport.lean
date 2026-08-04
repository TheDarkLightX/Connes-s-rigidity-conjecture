import LeanMathlib.Order.BooleanIntervalTransport

namespace LeanMathlib

section Ici

variable {α : Type*} [BooleanAlgebra α]

instance Set.Ici.instDistribLattice {u : α} : DistribLattice (Set.Ici u) :=
  Subtype.distribLattice
    (Psup := fun _ _ hx _ => le_trans hx le_sup_left)
    (Pinf := fun _ _ hx hy => le_inf hx hy)

noncomputable instance Set.Ici.instComplementedLattice {u : α} :
    ComplementedLattice (Set.Ici u) where
  exists_isCompl x := by
    refine ⟨⟨u ⊔ (x : α)ᶜ, le_sup_left⟩, ?_⟩
    rw [Set.Ici.isCompl_iff]
    constructor
    · calc
        (x : α) ⊓ (u ⊔ (x : α)ᶜ) = (x : α) ⊓ u ⊔ (x : α) ⊓ (x : α)ᶜ := by
          rw [inf_sup_left]
        _ = u ⊔ ⊥ := by rw [inf_eq_right.mpr x.prop, inf_compl_eq_bot]
        _ = u := by simp
    · rw [codisjoint_iff]
      calc
        (x : α) ⊔ (u ⊔ (x : α)ᶜ) = ((x : α) ⊔ u) ⊔ (x : α)ᶜ := by rw [sup_assoc]
        _ = (x : α) ⊔ (x : α)ᶜ := by rw [sup_eq_left.mpr x.prop]
        _ = ⊤ := sup_compl_eq_top

noncomputable instance Set.Ici.instBooleanAlgebra {u : α} : BooleanAlgebra (Set.Ici u) :=
  DistribLattice.booleanAlgebraOfComplemented (Set.Ici u)

theorem ici_isCoatom_iff_coe_isCoatom {u : α} {p : Set.Ici u} :
    IsCoatom p ↔ IsCoatom (p : α) := by
  refine ⟨IsCoatom.of_isCoatom_coe_Ici, fun hp => ?_⟩
  simpa using hp.Ici p.prop

theorem ici_eq_iff_forall_coe_coatoms {u : α} [IsCoatomic α] {x y : Set.Ici u} :
    x = y ↔ ∀ p : α, IsCoatom p → u ≤ p → (x ≤ p ↔ y ≤ p) := by
  simpa using
    (iic_eq_iff_forall_coe_atoms (α := αᵒᵈ) (u := u) (x := x) (y := y))

theorem ici_ne_iff_exists_coe_coatom_witness {u : α} [IsCoatomic α] {x y : Set.Ici u} :
    x ≠ y ↔
      (∃ p : α, IsCoatom p ∧ u ≤ p ∧ x ≤ p ∧ Codisjoint p y) ∨
      (∃ p : α, IsCoatom p ∧ u ≤ p ∧ y ≤ p ∧ Codisjoint p x) := by
  simpa using
    (iic_ne_iff_exists_coe_atom_witness (α := αᵒᵈ) (u := u) (x := x) (y := y))

end Ici

end LeanMathlib
