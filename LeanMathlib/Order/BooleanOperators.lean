import LeanMathlib.Order.BooleanDecomposition
import Mathlib.Order.Hom.BoundedLattice

namespace LeanMathlib

namespace SupBotHom

variable {α β γ : Type*} [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

/--
Complement-conjugate dual of a join-preserving bottom-preserving Boolean operator.

This is the standard Boolean-algebra-with-operators passage from a normal operator
to its De Morgan dual.
-/
def complDual (f : SupBotHom α β) : InfTopHom α β where
  toFun a := (f aᶜ)ᶜ
  map_inf' := by
    intro a b
    simp [map_sup, compl_sup]
  map_top' := by
    simp

@[simp] theorem complDual_apply (f : SupBotHom α β) (a : α) :
    complDual f a = (f aᶜ)ᶜ :=
  rfl

@[simp] theorem complDual_id :
    complDual (SupBotHom.id α) = InfTopHom.id α := by
  ext a
  simp [complDual]

@[simp] theorem complDual_comp (g : SupBotHom β γ) (f : SupBotHom α β) :
    complDual (g.comp f) = (complDual g).comp (complDual f) := by
  ext a
  simp [complDual]

/--
A Boolean operator preserves complement when it already acts like a full Boolean homomorphism.
-/
def PreservesCompl (f : SupBotHom α β) : Prop :=
  ∀ a, f aᶜ = (f a)ᶜ

theorem preservesCompl_iff_forall_complDual_eq
    (f : SupBotHom α β) :
    PreservesCompl f ↔ ∀ a, complDual f a = f a := by
  constructor
  · intro hcompl a
    simp [complDual, hcompl a]
  · intro hdual a
    simpa [complDual] using (hdual aᶜ).symm

/--
Upgrade a complement-preserving normal Boolean operator to a full bounded-lattice homomorphism.
-/
def toBoundedLatticeHom (f : SupBotHom α β) (hcompl : PreservesCompl f) :
    BoundedLatticeHom α β where
  toFun := f
  map_sup' := f.map_sup'
  map_inf' := by
    intro a b
    calc
      f (a ⊓ b) = f ((aᶜ ⊔ bᶜ)ᶜ) := by simp
      _ = (f (aᶜ ⊔ bᶜ))ᶜ := by rw [hcompl _]
      _ = (f aᶜ ⊔ f bᶜ)ᶜ := by
        have hsup : f (aᶜ ⊔ bᶜ) = f aᶜ ⊔ f bᶜ := f.map_sup' aᶜ bᶜ
        exact congrArg (fun x : β => xᶜ) hsup
      _ = ((f a)ᶜ ⊔ (f b)ᶜ)ᶜ := by rw [hcompl a, hcompl b]
      _ = f a ⊓ f b := by simp
  map_top' := by
    calc
      f ⊤ = f (⊥ᶜ) := by simp
      _ = (f ⊥)ᶜ := by rw [hcompl _]
      _ = ⊤ := by simp
  map_bot' := f.map_bot'

@[simp] theorem toBoundedLatticeHom_apply (f : SupBotHom α β) (hcompl : PreservesCompl f) (a : α) :
    toBoundedLatticeHom f hcompl a = f a :=
  rfl

theorem leftSplit_complDual_eq_rightSplit_map_compl (f : SupBotHom α α) (a b : α) :
    leftSplit (f a) (complDual f b) = rightSplit (f a) (f bᶜ) := by
  simp [leftSplit, rightSplit, complDual, sdiff_eq]

theorem rightSplit_complDual_eq_leftSplit_map_compl (f : SupBotHom α α) (a b : α) :
    rightSplit (f a) (complDual f b) = leftSplit (f a) (f bᶜ) := by
  simp [leftSplit, rightSplit, complDual, sdiff_eq]

end SupBotHom

namespace InfTopHom

variable {α β γ : Type*} [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

/--
Complement-conjugate dual of a meet-preserving top-preserving Boolean operator.
-/
def complDual (f : InfTopHom α β) : SupBotHom α β where
  toFun a := (f aᶜ)ᶜ
  map_sup' := by
    intro a b
    simp [map_inf, compl_inf]
  map_bot' := by
    simp

@[simp] theorem complDual_apply (f : InfTopHom α β) (a : α) :
    complDual f a = (f aᶜ)ᶜ :=
  rfl

@[simp] theorem complDual_id :
    complDual (InfTopHom.id α) = SupBotHom.id α := by
  ext a
  simp [complDual]

@[simp] theorem complDual_comp (g : InfTopHom β γ) (f : InfTopHom α β) :
    complDual (g.comp f) = (complDual g).comp (complDual f) := by
  ext a
  simp [complDual]

@[simp] theorem complDual_complDual (f : InfTopHom α β) :
    SupBotHom.complDual (complDual f) = f := by
  ext a
  simp [SupBotHom.complDual, complDual]

end InfTopHom

@[simp] theorem SupBotHom.complDual_complDual {α β : Type*}
    [BooleanAlgebra α] [BooleanAlgebra β] (f : SupBotHom α β) :
    InfTopHom.complDual (SupBotHom.complDual f) = f := by
  ext a
  simp [SupBotHom.complDual, InfTopHom.complDual]

end LeanMathlib
