import Mathlib
import LeanMathlib.Rigidity.TernaryShiftedCarry

namespace LeanMathlib.Rigidity

/-- Monomial basis indices for three polynomial coordinates. -/
abbrev PolynomialVectorBasisIndex := Σ _ : Fin 3, ℕ

/-- Standard coordinatewise monomial basis of `𝔽₃[t]^3`. -/
noncomputable def polynomialVectorBasis :
    Module.Basis PolynomialVectorBasisIndex (ZMod 3)
      (PolynomialVector3 (ZMod 3)) :=
  Pi.basis fun _ : Fin 3 => Polynomial.basisMonomials (ZMod 3)

@[simp]
theorem polynomialVectorBasis_apply
    (i : Fin 3) (k : ℕ) :
    polynomialVectorBasis ⟨i, k⟩ =
      Pi.single i ((Polynomial.X : Polynomial (ZMod 3)) ^ k) := by
  simp [polynomialVectorBasis, Polynomial.monomial_one_right_eq_X_pow]

/-- Algebraic duals are arbitrary coefficient functions on the monomial basis. -/
noncomputable def polynomialVectorDualEquivFun :
    PolynomialVectorDual ≃ₗ[ZMod 3]
      (PolynomialVectorBasisIndex → ZMod 3) :=
  ((polynomialVectorBasis).constr (ZMod 3)).symm

@[simp]
theorem polynomialVectorDualEquivFun_apply
    (ell : PolynomialVectorDual)
    (i : Fin 3) (k : ℕ) :
    polynomialVectorDualEquivFun ell ⟨i, k⟩ =
      ell (polynomialVectorBasis ⟨i, k⟩) := by
  rfl

/-- Multiplication by `t^n` shifts a monomial basis index by `n`. -/
theorem polynomialVectorShift_basis
    (n : ℕ) (i : Fin 3) (k : ℕ) :
    polynomialVectorShift n (polynomialVectorBasis ⟨i, k⟩) =
      polynomialVectorBasis ⟨i, n + k⟩ := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [polynomialVectorShift, polynomialVectorBasis_apply, Pi.single_apply,
      ← pow_add]
  · simp [polynomialVectorShift, polynomialVectorBasis_apply, Pi.single_apply,
      hji]

/-- In monomial coordinates, dual shift is tail shift by `n`. -/
theorem polynomialVectorDualShift_coordinate
    (n : ℕ) (ell : PolynomialVectorDual)
    (i : Fin 3) (k : ℕ) :
    polynomialVectorDualEquivFun (polynomialVectorDualShift n ell) ⟨i, k⟩ =
      polynomialVectorDualEquivFun ell ⟨i, n + k⟩ := by
  simp only [polynomialVectorDualEquivFun_apply,
    polynomialVectorDualShift_apply]
  rw [polynomialVectorShift_basis]

/-- Coordinate tail-shift linear map. -/
def polynomialDualCoordinateShift (n : ℕ) :
    (PolynomialVectorBasisIndex → ZMod 3) →ₗ[ZMod 3]
      (PolynomialVectorBasisIndex → ZMod 3) where
  toFun f ik := f ⟨ik.1, n + ik.2⟩
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl

@[simp]
theorem polynomialDualCoordinateShift_apply
    (n : ℕ) (f : PolynomialVectorBasisIndex → ZMod 3)
    (i : Fin 3) (k : ℕ) :
    polynomialDualCoordinateShift n f ⟨i, k⟩ = f ⟨i, n + k⟩ := rfl

/-- The dual-coordinate equivalence intertwines actual shift and tail shift. -/
theorem polynomialVectorDualEquivFun_shift
    (n : ℕ) (ell : PolynomialVectorDual) :
    polynomialVectorDualEquivFun (polynomialVectorDualShift n ell) =
      polynomialDualCoordinateShift n (polynomialVectorDualEquivFun ell) := by
  funext ik
  rcases ik with ⟨i, k⟩
  exact polynomialVectorDualShift_coordinate n ell i k

end LeanMathlib.Rigidity
