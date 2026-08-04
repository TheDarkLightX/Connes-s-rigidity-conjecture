import LeanMathlib.Order.BooleanSubalgebraWitnessTransport
import LeanMathlib.Order.BooleanOrderIsoTransport
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Heyting.Hom

namespace LeanMathlib

namespace BooleanSubalgebra

open scoped symmDiff

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem le_iff_of_injective (f : BoundedLatticeHom α β) (hf : Function.Injective f) {a b : α} :
    f a ≤ f b ↔ a ≤ b := by
  constructor
  · intro hab
    apply (inf_eq_left.1 ?_)
    apply hf
    calc
      f (a ⊓ b) = f a ⊓ f b := by simp
      _ = f a := inf_eq_left.2 hab
  · intro hab
    apply (inf_eq_left.1 ?_)
    calc
      f a ⊓ f b = f (a ⊓ b) := by simp
      _ = f a := by simp [inf_eq_left.2 hab]

noncomputable def equivMap (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) : L ≃o L.map f where
  toEquiv := Equiv.ofBijective
    (fun a : L => (⟨f a, by exact ⟨a, a.prop, rfl⟩⟩ : L.map f))
    ⟨fun a b hab => by apply Subtype.ext; exact hf (Subtype.ext_iff.mp hab), fun b => by
      rcases b.prop with ⟨a, ha, hab⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      apply Subtype.ext
      simpa using hab⟩
  map_rel_iff' := by
    intro a b
    exact le_iff_of_injective f hf

@[simp] theorem coe_equivMap_apply (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) (a : L) :
    ((equivMap f hf L a : L.map f) : β) = f a := rfl

@[simp] theorem equivMap_apply_symmDiff (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) (x y : L) :
    equivMap f hf L (x ∆ y) = equivMap f hf L x ∆ equivMap f hf L y := by
  apply Subtype.ext
  simp [equivMap, map_symmDiff]

@[simp] theorem equivMap_apply_bihimp (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) (x y : L) :
    equivMap f hf L (x ⇔ y) = equivMap f hf L x ⇔ equivMap f hf L y := by
  apply Subtype.ext
  simp [equivMap, map_bihimp]

@[simp] theorem isAtomic_iff_equivMap (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) : IsAtomic (L.map f) ↔ IsAtomic L := by
  simpa using (OrderIso.isAtomic_iff (equivMap f hf L)).symm

@[simp] theorem isCoatomic_iff_equivMap (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) : IsCoatomic (L.map f) ↔ IsCoatomic L := by
  simpa using (OrderIso.isCoatomic_iff (equivMap f hf L)).symm

@[simp] theorem isAtomless_iff_equivMap (f : BoundedLatticeHom α β) (hf : Function.Injective f)
    (L : BooleanSubalgebra α) : IsAtomless (L.map f) ↔ IsAtomless L := by
  simpa using (LeanMathlib.OrderIso.isAtomless_iff (equivMap f hf L)).symm

@[simp] theorem isAtomic_iff_comap_equiv (e : β ≃o α) (L : BooleanSubalgebra α) :
    IsAtomic (L.comap (e : BoundedLatticeHom β α)) ↔ IsAtomic L := by
  rw [BooleanSubalgebra.comap_equiv_eq_map_symm]
  simpa using
    (isAtomic_iff_equivMap (f := (e.symm : BoundedLatticeHom α β))
      (hf := e.symm.injective) (L := L))

@[simp] theorem isCoatomic_iff_comap_equiv (e : β ≃o α) (L : BooleanSubalgebra α) :
    IsCoatomic (L.comap (e : BoundedLatticeHom β α)) ↔ IsCoatomic L := by
  rw [BooleanSubalgebra.comap_equiv_eq_map_symm]
  simpa using
    (isCoatomic_iff_equivMap (f := (e.symm : BoundedLatticeHom α β))
      (hf := e.symm.injective) (L := L))

@[simp] theorem isAtomless_iff_comap_equiv (e : β ≃o α) (L : BooleanSubalgebra α) :
    IsAtomless (L.comap (e : BoundedLatticeHom β α)) ↔ IsAtomless L := by
  rw [BooleanSubalgebra.comap_equiv_eq_map_symm]
  simpa using
    (isAtomless_iff_equivMap (f := (e.symm : BoundedLatticeHom α β))
      (hf := e.symm.injective) (L := L))

end BooleanAlgebra

end BooleanSubalgebra

end LeanMathlib
