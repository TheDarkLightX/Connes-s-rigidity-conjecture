import Mathlib
import LeanMathlib.Rigidity.AbelianCocycleExtension
import LeanMathlib.Rigidity.TernaryWittCarry

namespace LeanMathlib.Rigidity

/-- The ternary Witt carry as normalized symmetric additive cocycle data. -/
def ternaryCarryCocycle
    (R : Type*) [CommRing R] : NormalizedSymmetricAddCocycle R R where
  c := ternaryCarry
  zero_left := ternaryCarry_zero_left
  symmetric := ternaryCarry_comm
  cocycle := ternaryCarry_cocycle

/-- Length-two ternary Witt vectors in explicit carry coordinates. -/
abbrev TernaryWittExtension :=
  (ternaryCarryCocycle (ZMod 3)).Extension

/-- Constructor in carry coordinates. -/
def ternaryWittMk (a b : ZMod 3) : TernaryWittExtension := ⟨a, b⟩

@[simp]
theorem ternaryWittMk_base (a b : ZMod 3) :
    (ternaryWittMk a b).base = a := rfl

@[simp]
theorem ternaryWittMk_fiber (a b : ZMod 3) :
    (ternaryWittMk a b).fiber = b := rfl

/-- Three times a Witt vector is the embedded first coordinate. -/
theorem ternaryWitt_three_nsmul (x : TernaryWittExtension) :
    3 • x = (ternaryCarryCocycle (ZMod 3)).fiberHom x.base := by
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> native_decide

/-- Every length-two ternary Witt vector is killed by `9`. -/
theorem ternaryWitt_nine_nsmul (x : TernaryWittExtension) :
    9 • x = 0 := by
  rw [show 9 = 3 * 3 by norm_num, mul_nsmul, ternaryWitt_three_nsmul]
  change 3 • ((ternaryCarryCocycle (ZMod 3)).fiberHom x.base) = 0
  rw [← map_nsmul]
  simp

/-- The first-coordinate generator is not killed by `3`. -/
theorem ternaryWitt_three_nsmul_one_ne_zero :
    3 • ternaryWittMk 1 0 ≠ 0 := by
  rw [ternaryWitt_three_nsmul]
  intro h
  have hfiber := congrArg
    NormalizedSymmetricAddCocycle.Extension.fiber h
  simpa using hfiber

/-- The canonical first-coordinate generator has exact additive order `9`. -/
theorem ternaryWittMk_one_order_nine :
    addOrderOf (ternaryWittMk 1 0) = 9 := by
  apply addOrderOf_eq_prime_pow
  · norm_num
  · exact ternaryWitt_nine_nsmul _
  · intro h
    have hthree : 3 • ternaryWittMk 1 0 = 0 := by
      simpa [pow_two] using h
    exact ternaryWitt_three_nsmul_one_ne_zero hthree

end LeanMathlib.Rigidity
