import Mathlib
import LeanMathlib.Rigidity.AbelianCocycleExtension

namespace LeanMathlib.Rigidity

namespace NormalizedSymmetricAddCocycle

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (C : NormalizedSymmetricAddCocycle A B)

/-- Compatibility of base/fiber automorphisms with a cocycle. -/
def AutomorphismCompatible
    (eA : A ≃+ A) (eB : B ≃+ B) : Prop :=
  ∀ a a', eB (C.c a a') = C.c (eA a) (eA a')

/-- Compatible base and fiber automorphisms lift coordinatewise to the extension. -/
def extensionAddEquiv
    (eA : A ≃+ A) (eB : B ≃+ B)
    (hcompat : C.AutomorphismCompatible eA eB) :
    C.Extension ≃+ C.Extension where
  toFun x := ⟨eA x.base, eB x.fiber⟩
  invFun x := ⟨eA.symm x.base, eB.symm x.fiber⟩
  left_inv := by
    intro x
    ext <;> simp
  right_inv := by
    intro x
    ext <;> simp
  map_add' := by
    intro x y
    apply Extension.ext
    · simp
    · simp only [Extension.add_fiber]
      rw [map_add, map_add, hcompat]

@[simp]
theorem extensionAddEquiv_base
    (eA : A ≃+ A) (eB : B ≃+ B)
    (hcompat : C.AutomorphismCompatible eA eB)
    (x : C.Extension) :
    (C.extensionAddEquiv eA eB hcompat x).base = eA x.base := rfl

@[simp]
theorem extensionAddEquiv_fiber
    (eA : A ≃+ A) (eB : B ≃+ B)
    (hcompat : C.AutomorphismCompatible eA eB)
    (x : C.Extension) :
    (C.extensionAddEquiv eA eB hcompat x).fiber = eB x.fiber := rfl

/-- The identity automorphisms lift to the identity extension automorphism. -/
theorem extensionAddEquiv_refl :
    C.extensionAddEquiv (AddEquiv.refl A) (AddEquiv.refl B)
      (by intro a a'; rfl) = AddEquiv.refl C.Extension := by
  ext x <;> rfl

end NormalizedSymmetricAddCocycle

end LeanMathlib.Rigidity
