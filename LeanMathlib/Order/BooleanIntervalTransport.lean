import LeanMathlib.Order.AtomicSymmDiff
import LeanMathlib.Order.AtomlessBooleanAlgebra
import Mathlib.Order.LatticeIntervals

namespace LeanMathlib

section Iic

variable {α : Type*} [BooleanAlgebra α]

instance Set.Iic.instDistribLattice {u : α} : DistribLattice (Set.Iic u) :=
  Subtype.distribLattice
    (Psup := fun _ _ hx hy => sup_le hx hy)
    (Pinf := fun _ _ hx _ => le_trans inf_le_left hx)

noncomputable instance Set.Iic.instComplementedLattice {u : α} :
    ComplementedLattice (Set.Iic u) where
  exists_isCompl x := by
    refine ⟨⟨u \ x, sdiff_le⟩, ?_⟩
    rw [Set.Iic.isCompl_iff]
    constructor
    · simpa using (disjoint_sdiff_self_right : Disjoint (x : α) (u \ x))
    · simpa using (sup_sdiff_cancel_right x.prop : (x : α) ⊔ (u \ x) = u)

noncomputable instance Set.Iic.instBooleanAlgebra {u : α} : BooleanAlgebra (Set.Iic u) :=
  DistribLattice.booleanAlgebraOfComplemented (Set.Iic u)

theorem iic_isAtom_iff_coe_isAtom {u : α} {p : Set.Iic u} :
    IsAtom p ↔ IsAtom (p : α) := by
  refine ⟨IsAtom.of_isAtom_coe_Iic, fun hp => ?_⟩
  simpa using hp.Iic p.prop

instance Set.Iic.instIsAtomless [IsAtomless α] {u : α} : IsAtomless (Set.Iic u) where
  exists_lt_nonzero := by
    intro a ha
    have ha0 : (a : α) ≠ ⊥ := by
      intro hbot
      apply ha
      ext
      simpa using hbot
    obtain ⟨b, hb0, hba⟩ := exists_lt_nonzero (α := α) (a := (a : α)) ha0
    refine ⟨⟨b, hba.le.trans a.prop⟩, ?_, ?_⟩
    · intro hb
      apply hb0
      simpa using congrArg (fun z : Set.Iic u => (z : α)) hb
    · exact hba

theorem iic_eq_iff_forall_coe_atoms {u : α} [IsAtomic α] {x y : Set.Iic u} :
    x = y ↔ ∀ p : α, IsAtom p → p ≤ u → (p ≤ x ↔ p ≤ y) := by
  refine ⟨fun h p hp hpu => h ▸ Iff.rfl, fun h => ?_⟩
  exact (BooleanAlgebra.eq_iff_atom_le_iff (x := x) (y := y)).2 fun p hp =>
    h p ((iic_isAtom_iff_coe_isAtom).1 hp) p.prop

theorem iic_ne_iff_exists_coe_atom_witness {u : α} [IsAtomic α] {x y : Set.Iic u} :
    x ≠ y ↔
      (∃ p : α, IsAtom p ∧ p ≤ u ∧ p ≤ x ∧ Disjoint p y) ∨
      (∃ p : α, IsAtom p ∧ p ≤ u ∧ p ≤ y ∧ Disjoint p x) := by
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases (ne_iff_exists_atom_witness (a := x) (b := y)).1 hxy with h | h
    · left
      rcases h with ⟨p, hp, hpx, hpdy⟩
      refine ⟨p, (iic_isAtom_iff_coe_isAtom).1 hp, p.prop, hpx, ?_⟩
      exact (Set.Iic.disjoint_iff (x := p) (y := y)).1 hpdy
    · right
      rcases h with ⟨p, hp, hpy, hpdx⟩
      refine ⟨p, (iic_isAtom_iff_coe_isAtom).1 hp, p.prop, hpy, ?_⟩
      exact (Set.Iic.disjoint_iff (x := p) (y := x)).1 hpdx
  · rcases hxy with hxy | hxy
    · refine (ne_iff_exists_atom_witness (a := x) (b := y)).2 ?_
      left
      rcases hxy with ⟨p, hp, hpu, hpx, hpdy⟩
      refine ⟨⟨p, hpu⟩, ?_, hpx, ?_⟩
      · simpa using hp.Iic hpu
      · exact (Set.Iic.disjoint_iff (x := ⟨p, hpu⟩) (y := y)).2 hpdy
    · refine (ne_iff_exists_atom_witness (a := x) (b := y)).2 ?_
      right
      rcases hxy with ⟨p, hp, hpu, hpy, hpdx⟩
      refine ⟨⟨p, hpu⟩, ?_, hpy, ?_⟩
      · simpa using hp.Iic hpu
      · exact (Set.Iic.disjoint_iff (x := ⟨p, hpu⟩) (y := x)).2 hpdx

end Iic

end LeanMathlib
