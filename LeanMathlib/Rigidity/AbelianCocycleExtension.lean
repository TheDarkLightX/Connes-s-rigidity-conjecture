import Mathlib

namespace LeanMathlib.Rigidity

/-- Normalized symmetric additive `2`-cocycle data. -/
structure NormalizedSymmetricAddCocycle
    (A B : Type*) [AddCommGroup A] [AddCommGroup B] where
  c : A → A → B
  zero_left : ∀ a, c 0 a = 0
  symmetric : ∀ a b, c a b = c b a
  cocycle : ∀ a b d, c a b + c (a + b) d = c b d + c a (b + d)

namespace NormalizedSymmetricAddCocycle

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (C : NormalizedSymmetricAddCocycle A B)

@[simp]
theorem zero_right (a : A) : C.c a 0 = 0 := by
  rw [C.symmetric, C.zero_left]

/-- The carrier of the abelian extension defined by a cocycle. -/
@[ext]
structure Extension (C : NormalizedSymmetricAddCocycle A B) where
  base : A
  fiber : B

namespace Extension

instance : Zero C.Extension := ⟨⟨0, 0⟩⟩

instance : Add C.Extension where
  add x y := ⟨x.base + y.base, x.fiber + y.fiber + C.c x.base y.base⟩

instance : Neg C.Extension where
  neg x :=
    ⟨-x.base, -x.fiber - C.c x.base (-x.base)⟩

@[simp]
theorem zero_base : (0 : C.Extension).base = 0 := rfl

@[simp]
theorem zero_fiber : (0 : C.Extension).fiber = 0 := rfl

@[simp]
theorem add_base (x y : C.Extension) :
    (x + y).base = x.base + y.base := rfl

@[simp]
theorem add_fiber (x y : C.Extension) :
    (x + y).fiber = x.fiber + y.fiber + C.c x.base y.base := rfl

@[simp]
theorem neg_base (x : C.Extension) :
    (-x).base = -x.base := rfl

@[simp]
theorem neg_fiber (x : C.Extension) :
    (-x).fiber = -x.fiber - C.c x.base (-x.base) := rfl

instance : AddCommGroup C.Extension where
  add_assoc x y z := by
    apply Extension.ext
    · simp [add_assoc]
    · simp only [add_fiber, add_base]
      rw [C.cocycle]
      abel
  zero_add x := by
    apply Extension.ext
    · simp
    · simp [C.zero_left]
  add_zero x := by
    apply Extension.ext
    · simp
    · simp
  neg_add_cancel x := by
    apply Extension.ext
    · simp
    · simp
  add_comm x y := by
    apply Extension.ext
    · simp [add_comm]
    · simp only [add_fiber]
      rw [C.symmetric]
      abel
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Canonical inclusion of the fiber subgroup. -/
def fiberHom : B →+ C.Extension where
  toFun b := ⟨0, b⟩
  map_zero' := rfl
  map_add' x y := by
    ext <;> simp [C.zero_left]

/-- Canonical projection to the base group. -/
def baseHom : C.Extension →+ A where
  toFun x := x.base
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem baseHom_apply (x : C.Extension) : C.baseHom x = x.base := rfl

@[simp]
theorem fiberHom_base (b : B) : (C.fiberHom b).base = 0 := rfl

@[simp]
theorem fiberHom_fiber (b : B) : (C.fiberHom b).fiber = b := rfl

/-- The fiber inclusion is injective. -/
theorem fiberHom_injective : Function.Injective C.fiberHom := by
  intro x y h
  exact congrArg (fun z : C.Extension => z.fiber) h

/-- The base projection is surjective. -/
theorem baseHom_surjective : Function.Surjective C.baseHom := by
  intro a
  exact ⟨⟨a, 0⟩, rfl⟩

/-- The kernel of the base projection is exactly the embedded fiber. -/
theorem mem_ker_baseHom_iff (x : C.Extension) :
    x ∈ C.baseHom.ker ↔ ∃ b, x = C.fiberHom b := by
  constructor
  · intro hx
    have hbase : x.base = 0 := hx
    exact ⟨x.fiber, by ext <;> simp [hbase]⟩
  · rintro ⟨b, rfl⟩
    simp

end Extension
end NormalizedSymmetricAddCocycle

end LeanMathlib.Rigidity
