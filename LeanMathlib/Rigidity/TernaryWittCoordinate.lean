import Mathlib
import LeanMathlib.Rigidity.TernaryWittExtension

namespace LeanMathlib.Rigidity

/--
The Teichmüller coordinate from the explicit scalar ternary Witt extension to
`ZMod 9`. Representatives `0,1,2` are lifted by their cubes `0,1,8` modulo 9.
-/
def ternaryTeichCoordinate (x : TernaryWittExtension) : ZMod 9 :=
  ((x.base.val ^ 3 + 3 * x.fiber.val : ℕ) : ZMod 9)

@[simp]
theorem ternaryTeichCoordinate_mk (a b : ZMod 3) :
    ternaryTeichCoordinate (ternaryWittMk a b) =
      ((a.val ^ 3 + 3 * b.val : ℕ) : ZMod 9) := rfl

/--
The cubic coordinate transports the ternary carry addition to ordinary
addition modulo 9. This is an exhaustive proof over the nine scalar states.
-/
theorem ternaryTeichCoordinate_add (x y : TernaryWittExtension) :
    ternaryTeichCoordinate (x + y) =
      ternaryTeichCoordinate x + ternaryTeichCoordinate y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    decide

@[simp]
theorem ternaryTeichCoordinate_zero :
    ternaryTeichCoordinate (0 : TernaryWittExtension) = 0 := by
  decide

/-- The scalar Teichmüller coordinate is injective on the nine Witt states. -/
theorem ternaryTeichCoordinate_injective :
    Function.Injective ternaryTeichCoordinate := by
  intro x y h
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  apply NormalizedSymmetricAddCocycle.Extension.ext
  · revert h
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      decide
  · revert h
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      decide

/-- The scalar Teichmüller coordinate is surjective onto `ZMod 9`. -/
theorem ternaryTeichCoordinate_surjective :
    Function.Surjective ternaryTeichCoordinate := by
  intro z
  fin_cases z
  · exact ⟨ternaryWittMk 0 0, by decide⟩
  · exact ⟨ternaryWittMk 1 0, by decide⟩
  · exact ⟨ternaryWittMk 2 1, by decide⟩
  · exact ⟨ternaryWittMk 0 1, by decide⟩
  · exact ⟨ternaryWittMk 1 1, by decide⟩
  · exact ⟨ternaryWittMk 2 2, by decide⟩
  · exact ⟨ternaryWittMk 0 2, by decide⟩
  · exact ⟨ternaryWittMk 1 2, by decide⟩
  · exact ⟨ternaryWittMk 2 0, by decide⟩

/--
The scalar length-two ternary Witt extension is additively equivalent to
`ZMod 9` through the cubic Teichmüller coordinate.
-/
noncomputable def ternaryWittAddEquivZMod9 :
    TernaryWittExtension ≃+ ZMod 9 :=
  AddEquiv.ofBijective
    ({ toFun := ternaryTeichCoordinate
       map_zero' := ternaryTeichCoordinate_zero
       map_add' := ternaryTeichCoordinate_add } :
      TernaryWittExtension →+ ZMod 9)
    ⟨ternaryTeichCoordinate_injective, ternaryTeichCoordinate_surjective⟩

@[simp]
theorem ternaryWittAddEquivZMod9_apply (x : TernaryWittExtension) :
    ternaryWittAddEquivZMod9 x = ternaryTeichCoordinate x := rfl

end LeanMathlib.Rigidity
