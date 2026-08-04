import Mathlib
import LeanMathlib.Rigidity.TripleExponentBlock

namespace LeanMathlib.Rigidity

/-- Triple tensor product of one-variable polynomial modules. -/
abbrev PolynomialTensorCube (F : Type*) [Field F] :=
  TensorProduct F (Polynomial F)
    (TensorProduct F (Polynomial F) (Polynomial F))

/-- Reindex nested tensor-basis indices by explicit exponent triples. -/
def nestedExponentEquiv : (ℕ × (ℕ × ℕ)) ≃ TripleExponent where
  toFun e := ⟨e.1, e.2.1, e.2.2⟩
  invFun e := (e.first, (e.second, e.third))
  left_inv := by intro e; rcases e with ⟨a, b, c⟩; rfl
  right_inv := by intro e; cases e; rfl

/-- Monomial tensor basis indexed by three exponents. -/
noncomputable def polynomialTensorCubeBasis
    (F : Type*) [Field F] :
    Module.Basis TripleExponent F (PolynomialTensorCube F) :=
  ((Polynomial.basisMonomials F).tensorProduct
      ((Polynomial.basisMonomials F).tensorProduct
        (Polynomial.basisMonomials F))).reindex nestedExponentEquiv

/-- Coordinate equivalence from a triple polynomial tensor to a finite exponent block. -/
noncomputable def polynomialTensorCubeCoefficients
    (F : Type*) [Field F] :
    PolynomialTensorCube F ≃ₗ[F] TripleBlock F :=
  (polynomialTensorCubeBasis F).repr

/-- The tensor monomial basis vector has the expected nested pure-tensor form. -/
@[simp]
theorem polynomialTensorCubeBasis_apply
    (F : Type*) [Field F] (e : TripleExponent) :
    polynomialTensorCubeBasis F e =
      Polynomial.monomial e.first 1 ⊗ₜ[F]
        (Polynomial.monomial e.second 1 ⊗ₜ[F]
          Polynomial.monomial e.third 1) := by
  rw [polynomialTensorCubeBasis, Module.Basis.reindex_apply]
  simp [nestedExponentEquiv]

/-- Pure tensor coefficients factor as the product of the three polynomial coefficients. -/
@[simp]
theorem polynomialTensorCubeCoefficients_tmul
    (F : Type*) [Field F]
    (u v z : Polynomial F) (e : TripleExponent) :
    polynomialTensorCubeCoefficients F (u ⊗ₜ[F] (v ⊗ₜ[F] z)) e =
      u.coeff e.first * v.coeff e.second * z.coeff e.third := by
  unfold polynomialTensorCubeCoefficients polynomialTensorCubeBasis
  rw [Module.Basis.repr_reindex_apply,
    Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [smul_eq_mul]
  ring

end LeanMathlib.Rigidity
