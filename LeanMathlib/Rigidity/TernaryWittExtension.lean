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
  apply NormalizedSymmetricAddCocycle.Extension.ext
  · fin_cases a <;> fin_cases b <;> decide
  · fin_cases a <;> fin_cases b <;> decide

/-- Every length-two ternary Witt vector is killed by `9`. -/
theorem ternaryWitt_nine_nsmul (x : TernaryWittExtension) :
    9 • x = 0 := by
  let C := ternaryCarryCocycle (ZMod 3)
  calc
    9 • x = (3 * 3) • x := by norm_num
    _ = 3 • (3 • x) := by rw [mul_nsmul]
    _ = 3 • C.fiberHom x.base := by
      rw [ternaryWitt_three_nsmul x]
    _ = C.fiberHom (3 • x.base) := by
      exact ((C.fiberHom).map_nsmul x.base 3).symm
    _ = C.fiberHom 0 := by
      congr 1
      have hchar : ∀ a : ZMod 3, 3 • a = 0 := by
        intro a
        fin_cases a <;> decide
      exact hchar x.base
    _ = 0 := (C.fiberHom).map_zero

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
  have hthree :
      ¬(3 ^ 1 : ℕ) • ternaryWittMk 1 0 = 0 := by
    simpa using ternaryWitt_three_nsmul_one_ne_zero
  have hnine :
      (3 ^ (1 + 1) : ℕ) • ternaryWittMk 1 0 = 0 := by
    norm_num
    exact ternaryWitt_nine_nsmul _
  have horder := addOrderOf_eq_prime_pow
    (x := ternaryWittMk 1 0) (p := 3) (n := 1) hthree hnine
  norm_num at horder
  exact horder

end LeanMathlib.Rigidity
