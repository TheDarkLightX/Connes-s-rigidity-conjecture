import Mathlib
import LeanMathlib.Rigidity.TernaryFunctionalCarry

namespace LeanMathlib.Rigidity

/-- Multiply every polynomial-vector coordinate by `X^n`. -/
def polynomialVectorShift (n : ℕ) :
    PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3) where
  toFun v i := (Polynomial.X : Polynomial (ZMod 3)) ^ n * v i
  map_add' := by
    intro u v
    funext i
    simp [mul_add]
  map_smul' := by
    intro c v
    funext i
    simp [mul_assoc, mul_left_comm, mul_comm]

@[simp]
theorem polynomialVectorShift_apply
    (n : ℕ) (v : PolynomialVector3 (ZMod 3)) (i : Fin 3) :
    polynomialVectorShift n v i =
      (Polynomial.X : Polynomial (ZMod 3)) ^ n * v i := rfl

/-- Pull a dual functional back along multiplication by `X^n`. -/
noncomputable def polynomialVectorDualShift (n : ℕ) :
    PolynomialVectorDual →ₗ[ZMod 3] PolynomialVectorDual where
  toFun ell := ell.comp (polynomialVectorShift n)
  map_add' := by
    intro ell m
    ext v
    simp
  map_smul' := by
    intro c ell
    ext v
    simp

@[simp]
theorem polynomialVectorDualShift_apply
    (n : ℕ) (ell : PolynomialVectorDual)
    (v : PolynomialVector3 (ZMod 3)) :
    polynomialVectorDualShift n ell v = ell (polynomialVectorShift n v) := rfl

/-- Carry cocycle shifted by `t^n` on the base dual. -/
noncomputable def ternaryShiftedFunctionalCarry
    (n : ℕ) (ell m : PolynomialVectorDual) : DividedCubeDual :=
  ternaryFunctionalCarry
    (polynomialVectorDualShift n ell)
    (polynomialVectorDualShift n m)

@[simp]
theorem ternaryShiftedFunctionalCarry_zero_left
    (n : ℕ) (ell : PolynomialVectorDual) :
    ternaryShiftedFunctionalCarry n 0 ell = 0 := by
  simp [ternaryShiftedFunctionalCarry]

/-- Shifted carry remains symmetric. -/
theorem ternaryShiftedFunctionalCarry_comm
    (n : ℕ) (ell m : PolynomialVectorDual) :
    ternaryShiftedFunctionalCarry n ell m =
      ternaryShiftedFunctionalCarry n m ell := by
  exact ternaryFunctionalCarry_comm _ _

/-- Shifted carry satisfies the additive cocycle identity. -/
theorem ternaryShiftedFunctionalCarry_cocycle
    (n : ℕ) (ell m d : PolynomialVectorDual) :
    ternaryShiftedFunctionalCarry n ell m +
        ternaryShiftedFunctionalCarry n (ell + m) d =
      ternaryShiftedFunctionalCarry n m d +
        ternaryShiftedFunctionalCarry n ell (m + d) := by
  simpa [ternaryShiftedFunctionalCarry, map_add] using
    ternaryFunctionalCarry_cocycle
      (polynomialVectorDualShift n ell)
      (polynomialVectorDualShift n m)
      (polynomialVectorDualShift n d)

/-- Shifted ternary carry as normalized symmetric cocycle data. -/
noncomputable def ternaryShiftedFunctionalCarryCocycle (n : ℕ) :
    NormalizedSymmetricAddCocycle PolynomialVectorDual DividedCubeDual where
  c := ternaryShiftedFunctionalCarry n
  zero_left := ternaryShiftedFunctionalCarry_zero_left n
  symmetric := ternaryShiftedFunctionalCarry_comm n
  cocycle := ternaryShiftedFunctionalCarry_cocycle n

/-- Algebraic compact-dual carry group at shift `n`. -/
abbrev TernaryShiftedCarryExtension (n : ℕ) :=
  (ternaryShiftedFunctionalCarryCocycle n).Extension

/-- All shifted carry groups have the same underlying coordinate set. -/
def ternaryShiftedCarryUnderlyingEquiv (n m : ℕ) :
    TernaryShiftedCarryExtension n ≃ TernaryShiftedCarryExtension m where
  toFun x := ⟨x.base, x.fiber⟩
  invFun x := ⟨x.base, x.fiber⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

@[simp]
theorem ternaryShiftedCarryUnderlyingEquiv_base
    (n m : ℕ) (x : TernaryShiftedCarryExtension n) :
    (ternaryShiftedCarryUnderlyingEquiv n m x).base = x.base := rfl

@[simp]
theorem ternaryShiftedCarryUnderlyingEquiv_fiber
    (n m : ℕ) (x : TernaryShiftedCarryExtension n) :
    (ternaryShiftedCarryUnderlyingEquiv n m x).fiber = x.fiber := rfl

end LeanMathlib.Rigidity
