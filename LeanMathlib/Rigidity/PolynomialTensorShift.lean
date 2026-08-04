import Mathlib
import LeanMathlib.Rigidity.PolynomialTensorCubeBasis
import LeanMathlib.Rigidity.CubeCoordinateTransvection

namespace LeanMathlib.Rigidity

/-- First-exponent shift as a linear map on coefficient blocks. -/
def shiftFirstBlockLinear
    (F : Type*) [Field F] (n : ℕ) : TripleBlock F →ₗ[F] TripleBlock F where
  toFun := singleShiftTerm n
  map_add' := by
    intro A B
    ext e
    classical
    simp [singleShiftTerm, Finsupp.embDomain_apply]
  map_smul' := by
    intro c A
    ext e
    classical
    simp [singleShiftTerm, Finsupp.embDomain_apply]

/-- Second-exponent shift as a linear map on coefficient blocks. -/
def shiftSecondBlockLinear
    (F : Type*) [Field F] (n : ℕ) : TripleBlock F →ₗ[F] TripleBlock F where
  toFun := negativeShiftTerm n
  map_add' := by
    intro A B
    ext e
    classical
    simp [negativeShiftTerm, Finsupp.embDomain_apply]
  map_smul' := by
    intro c A
    ext e
    classical
    simp [negativeShiftTerm, Finsupp.embDomain_apply]

/-- Multiply the first polynomial tensor factor by `X^n`. -/
noncomputable def multiplyFirstPolynomialTensor
    (F : Type*) [Field F] (n : ℕ) :
    PolynomialTensorCube F →ₗ[F] PolynomialTensorCube F :=
  TensorProduct.map
    (LinearMap.mulLeft F ((Polynomial.X : Polynomial F) ^ n))
    LinearMap.id

/-- Multiply the second polynomial tensor factor by `X^n`. -/
noncomputable def multiplySecondPolynomialTensor
    (F : Type*) [Field F] (n : ℕ) :
    PolynomialTensorCube F →ₗ[F] PolynomialTensorCube F :=
  TensorProduct.map LinearMap.id <|
    TensorProduct.map
      (LinearMap.mulLeft F ((Polynomial.X : Polynomial F) ^ n))
      LinearMap.id

/-- Multiplication in the first tensor factor shifts the monomial basis index. -/
theorem multiplyFirstPolynomialTensor_basis
    (F : Type*) [Field F] (n : ℕ) (e : TripleExponent) :
    multiplyFirstPolynomialTensor F n (polynomialTensorCubeBasis F e) =
      polynomialTensorCubeBasis F (TripleExponent.shiftFirst n e) := by
  simp [multiplyFirstPolynomialTensor, polynomialTensorCubeBasis_apply,
    TripleExponent.shiftFirst, ← pow_add]
  congr 2
  omega

/-- Multiplication in the second tensor factor shifts the monomial basis index. -/
theorem multiplySecondPolynomialTensor_basis
    (F : Type*) [Field F] (n : ℕ) (e : TripleExponent) :
    multiplySecondPolynomialTensor F n (polynomialTensorCubeBasis F e) =
      polynomialTensorCubeBasis F (TripleExponent.shiftSecond n e) := by
  simp [multiplySecondPolynomialTensor, polynomialTensorCubeBasis_apply,
    TripleExponent.shiftSecond, ← pow_add]
  congr 2
  omega

/-- First-factor tensor multiplication is exactly first-exponent coefficient shift. -/
theorem polynomialTensorCubeCoefficients_multiplyFirst
    (F : Type*) [Field F] (n : ℕ) (w : PolynomialTensorCube F) :
    polynomialTensorCubeCoefficients F (multiplyFirstPolynomialTensor F n w) =
      singleShiftTerm n (polynomialTensorCubeCoefficients F w) := by
  let L : PolynomialTensorCube F →ₗ[F] TripleBlock F :=
    (polynomialTensorCubeCoefficients F).toLinearMap.comp
      (multiplyFirstPolynomialTensor F n)
  let R : PolynomialTensorCube F →ₗ[F] TripleBlock F :=
    (shiftFirstBlockLinear F n).comp
      (polynomialTensorCubeCoefficients F).toLinearMap
  have hLR : L = R := by
    apply (polynomialTensorCubeBasis F).ext
    intro e
    change polynomialTensorCubeCoefficients F
        (multiplyFirstPolynomialTensor F n (polynomialTensorCubeBasis F e)) =
      singleShiftTerm n
        (polynomialTensorCubeCoefficients F (polynomialTensorCubeBasis F e))
    rw [multiplyFirstPolynomialTensor_basis]
    simp [polynomialTensorCubeCoefficients, singleShiftTerm]
  exact DFunLike.congr_fun hLR w

/-- Second-factor tensor multiplication is exactly second-exponent coefficient shift. -/
theorem polynomialTensorCubeCoefficients_multiplySecond
    (F : Type*) [Field F] (n : ℕ) (w : PolynomialTensorCube F) :
    polynomialTensorCubeCoefficients F (multiplySecondPolynomialTensor F n w) =
      negativeShiftTerm n (polynomialTensorCubeCoefficients F w) := by
  let L : PolynomialTensorCube F →ₗ[F] TripleBlock F :=
    (polynomialTensorCubeCoefficients F).toLinearMap.comp
      (multiplySecondPolynomialTensor F n)
  let R : PolynomialTensorCube F →ₗ[F] TripleBlock F :=
    (shiftSecondBlockLinear F n).comp
      (polynomialTensorCubeCoefficients F).toLinearMap
  have hLR : L = R := by
    apply (polynomialTensorCubeBasis F).ext
    intro e
    change polynomialTensorCubeCoefficients F
        (multiplySecondPolynomialTensor F n (polynomialTensorCubeBasis F e)) =
      negativeShiftTerm n
        (polynomialTensorCubeCoefficients F (polynomialTensorCubeBasis F e))
    rw [multiplySecondPolynomialTensor_basis]
    simp [polynomialTensorCubeCoefficients, negativeShiftTerm]
  exact DFunLike.congr_fun hLR w

/-- Multiplication in both first and second tensor factors gives the double shift. -/
theorem polynomialTensorCubeCoefficients_multiplyFirstSecond
    (F : Type*) [Field F] (n : ℕ) (w : PolynomialTensorCube F) :
    polynomialTensorCubeCoefficients F
        (multiplySecondPolynomialTensor F n
          (multiplyFirstPolynomialTensor F n w)) =
      doubleShiftTerm n (polynomialTensorCubeCoefficients F w) := by
  rw [polynomialTensorCubeCoefficients_multiplySecond]
  rw [polynomialTensorCubeCoefficients_multiplyFirst]
  rfl

end LeanMathlib.Rigidity
