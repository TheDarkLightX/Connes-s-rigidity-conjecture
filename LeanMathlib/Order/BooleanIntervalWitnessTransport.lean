import LeanMathlib.Order.SymmDiffBihimpWitness
import LeanMathlib.Order.BooleanLowerIntervalTransport

namespace LeanMathlib

open scoped symmDiff

section Iic

variable {α : Type*} [BooleanAlgebra α] [IsAtomic α]

theorem iic_ne_iff_exists_coe_atom_disjoint_bihimp {u : α} {x y : Set.Iic u} :
    x ≠ y ↔ ∃ p : α, IsAtom p ∧ p ≤ u ∧ Disjoint p (((x ⇔ y : Set.Iic u) : α)) := by
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases (ne_iff_exists_atom_disjoint_bihimp (a := x) (b := y)).1 hxy with ⟨p, hp, hpd⟩
    refine ⟨p, (iic_isAtom_iff_coe_isAtom).1 hp, p.prop, ?_⟩
    exact (Set.Iic.disjoint_iff (x := p) (y := x ⇔ y)).1 hpd
  · rcases hxy with ⟨p, hp, hpu, hpd⟩
    refine (ne_iff_exists_atom_disjoint_bihimp (a := x) (b := y)).2 ?_
    refine ⟨⟨p, hpu⟩, ?_, ?_⟩
    · simpa using hp.Iic hpu
    · exact (Set.Iic.disjoint_iff (x := ⟨p, hpu⟩) (y := x ⇔ y)).2 hpd

theorem iic_eq_iff_forall_coe_atoms_not_disjoint_bihimp {u : α} {x y : Set.Iic u} :
    x = y ↔ ∀ p : α, IsAtom p → p ≤ u → ¬ Disjoint p (((x ⇔ y : Set.Iic u) : α)) := by
  refine ⟨fun h p hp hpu => ?_, fun h => ?_⟩
  · have hp' : IsAtom (⟨p, hpu⟩ : Set.Iic u) := by
      simpa using hp.Iic hpu
    have hnd : ¬ Disjoint (⟨p, hpu⟩ : Set.Iic u) (x ⇔ y) :=
      (eq_iff_forall_atom_not_disjoint_bihimp (a := x) (b := y)).1 h _ hp'
    intro hpd
    exact hnd ((Set.Iic.disjoint_iff (x := ⟨p, hpu⟩) (y := x ⇔ y)).2 hpd)
  · by_contra hxy
    rcases (iic_ne_iff_exists_coe_atom_disjoint_bihimp (x := x) (y := y)).1 hxy with
      ⟨p, hp, hpu, hpd⟩
    exact h p hp hpu hpd

end Iic

section Ici

variable {α : Type*} [BooleanAlgebra α] [IsCoatomic α]

theorem ici_ne_iff_exists_coe_coatom_codisjoint_symmDiff {u : α} {x y : Set.Ici u} :
    x ≠ y ↔ ∃ p : α, IsCoatom p ∧ u ≤ p ∧ Codisjoint p (((x ∆ y : Set.Ici u) : α)) := by
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases (ne_iff_exists_coatom_codisjoint_symmDiff (a := x) (b := y)).1 hxy with
      ⟨p, hp, hpc⟩
    refine ⟨p, (ici_isCoatom_iff_coe_isCoatom).1 hp, p.prop, ?_⟩
    exact (Set.Ici.codisjoint_iff (x := p) (y := x ∆ y)).1 hpc
  · rcases hxy with ⟨p, hp, hup, hpc⟩
    refine (ne_iff_exists_coatom_codisjoint_symmDiff (a := x) (b := y)).2 ?_
    refine ⟨⟨p, hup⟩, ?_, ?_⟩
    · simpa using hp.Ici hup
    · exact (Set.Ici.codisjoint_iff (x := ⟨p, hup⟩) (y := x ∆ y)).2 hpc

theorem ici_eq_iff_forall_coe_coatoms_not_codisjoint_symmDiff {u : α} {x y : Set.Ici u} :
    x = y ↔ ∀ p : α, IsCoatom p → u ≤ p → ¬ Codisjoint p (((x ∆ y : Set.Ici u) : α)) := by
  refine ⟨fun h p hp hup => ?_, fun h => ?_⟩
  · have hp' : IsCoatom (⟨p, hup⟩ : Set.Ici u) := by
      simpa using hp.Ici hup
    have hnc : ¬ Codisjoint (⟨p, hup⟩ : Set.Ici u) (x ∆ y) :=
      (eq_iff_forall_coatom_not_codisjoint_symmDiff (a := x) (b := y)).1 h _ hp'
    intro hpc
    exact hnc ((Set.Ici.codisjoint_iff (x := ⟨p, hup⟩) (y := x ∆ y)).2 hpc)
  · by_contra hxy
    rcases (ici_ne_iff_exists_coe_coatom_codisjoint_symmDiff (x := x) (y := y)).1 hxy with
      ⟨p, hp, hup, hpc⟩
    exact h p hp hup hpc

end Ici

end LeanMathlib
