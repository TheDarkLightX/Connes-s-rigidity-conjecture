import Mathlib
import LeanMathlib.Rigidity.PolynomialVectorTransvection
import LeanMathlib.Rigidity.PolynomialTensorShift

namespace LeanMathlib.Rigidity

/-- Diagonal action of an explicit polynomial transvection on the tensor cube. -/
noncomputable def polynomialTensorCubeTransvection
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ) :
    PolynomialVectorTensorCube F →ₗ[F] PolynomialVectorTensorCube F :=
  TensorProduct.map
    (polynomialVectorTransvection F target source n) <|
      TensorProduct.map
        (polynomialVectorTransvection F target source n)
        (polynomialVectorTransvection F target source n)

@[simp]
theorem polynomialTensorCubeTransvection_tmul
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (u v z : PolynomialVector3 F) :
    polynomialTensorCubeTransvection F target source n
        (u ⊗ₜ[F] (v ⊗ₜ[F] z)) =
      polynomialVectorTransvection F target source n u ⊗ₜ[F]
        (polynomialVectorTransvection F target source n v ⊗ₜ[F]
          polynomialVectorTransvection F target source n z) := by
  simp [polynomialTensorCubeTransvection]

/-- Coordinate-block action before taking monomial coefficients. -/
def firstTwoTransvectionTensorOutput
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (w : Fin 3 → Fin 3 → Fin 3 → PolynomialTensorCube F)
    (a b c : Fin 3) : PolynomialTensorCube F :=
  w a b c +
    (if a = target then multiplyFirstPolynomialTensor F n (w source b c) else 0) +
    (if b = target then multiplySecondPolynomialTensor F n (w a source c) else 0) +
    (if a = target ∧ b = target then
      multiplySecondPolynomialTensor F n
        (multiplyFirstPolynomialTensor F n (w source source c)) else 0)

/-- The block-level coordinate action on a pure tensor. -/
theorem polynomialTensorCubeTransvection_blockCoords_tmul
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (u v z : PolynomialVector3 F)
    (a b c : Fin 3) (hc : c ≠ target) :
    polynomialVectorTensorCubeBlockCoords F
        (polynomialTensorCubeTransvection F target source n
          (u ⊗ₜ[F] (v ⊗ₜ[F] z))) a b c =
      firstTwoTransvectionTensorOutput F target source n
        (polynomialVectorTensorCubeBlockCoords F
          (u ⊗ₜ[F] (v ⊗ₜ[F] z))) a b c := by
  by_cases ha : a = target <;> by_cases hb : b = target
  · subst a
    subst b
    simp [firstTwoTransvectionTensorOutput, polynomialTensorCubeTransvection,
      polynomialVectorTransvection, hc, multiplyFirstPolynomialTensor,
      multiplySecondPolynomialTensor, TensorProduct.add_tmul, TensorProduct.tmul_add,
      add_assoc, add_left_comm, add_comm]
  · subst a
    simp [firstTwoTransvectionTensorOutput, polynomialTensorCubeTransvection,
      polynomialVectorTransvection, hc, hb, multiplyFirstPolynomialTensor,
      multiplySecondPolynomialTensor, TensorProduct.add_tmul, TensorProduct.tmul_add,
      add_assoc, add_left_comm, add_comm]
  · subst b
    simp [firstTwoTransvectionTensorOutput, polynomialTensorCubeTransvection,
      polynomialVectorTransvection, hc, ha, multiplyFirstPolynomialTensor,
      multiplySecondPolynomialTensor, TensorProduct.add_tmul, TensorProduct.tmul_add,
      add_assoc, add_left_comm, add_comm]
  · simp [firstTwoTransvectionTensorOutput, polynomialTensorCubeTransvection,
      polynomialVectorTransvection, hc, ha, hb]

/-- The block coordinate action is additive in the tensor. -/
theorem firstTwoTransvectionTensorOutput_add
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (w₁ w₂ : Fin 3 → Fin 3 → Fin 3 → PolynomialTensorCube F)
    (a b c : Fin 3) :
    firstTwoTransvectionTensorOutput F target source n
        (w₁ + w₂) a b c =
      firstTwoTransvectionTensorOutput F target source n w₁ a b c +
        firstTwoTransvectionTensorOutput F target source n w₂ a b c := by
  by_cases ha : a = target <;> by_cases hb : b = target <;>
    simp [firstTwoTransvectionTensorOutput, ha, hb, map_add,
      add_assoc, add_left_comm, add_comm]

/-- Genuine tensor-cube action has the four-term block coordinate formula. -/
theorem polynomialTensorCubeTransvection_blockCoords
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (w : PolynomialVectorTensorCube F)
    (a b c : Fin 3) (hc : c ≠ target) :
    polynomialVectorTensorCubeBlockCoords F
        (polynomialTensorCubeTransvection F target source n w) a b c =
      firstTwoTransvectionTensorOutput F target source n
        (polynomialVectorTensorCubeBlockCoords F w) a b c := by
  induction w using TensorProduct.induction_on with
  | zero => simp [firstTwoTransvectionTensorOutput]
  | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
        firstTwoTransvectionTensorOutput_add]
      exact congrArg₂ (· + ·) hx hy
  | tmul u q =>
      induction q using TensorProduct.induction_on with
      | zero => simp [firstTwoTransvectionTensorOutput]
      | add x y hx hy =>
          rw [TensorProduct.tmul_add, map_add, map_add, Pi.add_apply, Pi.add_apply,
            Pi.add_apply, firstTwoTransvectionTensorOutput_add]
          exact congrArg₂ (· + ·) hx hy
      | tmul v z =>
          exact polynomialTensorCubeTransvection_blockCoords_tmul
            F target source n u v z a b c hc

/-- Taking monomial coefficients turns the genuine action into the coordinate formula. -/
theorem polynomialTensorCubeTransvection_coords
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (w : PolynomialVectorTensorCube F)
    (a b c : Fin 3) (hc : c ≠ target) :
    polynomialVectorTensorCubeCoords F
        (polynomialTensorCubeTransvection F target source n w) a b c =
      firstTwoTransvectionOutput target source n
        (polynomialVectorTensorCubeCoords F w) a b c := by
  have hblock := polynomialTensorCubeTransvection_blockCoords
    F target source n w a b c hc
  have h := congrArg (polynomialTensorCubeCoefficients F) hblock
  simpa [polynomialVectorTensorCubeCoords,
    firstTwoTransvectionTensorOutput, firstTwoTransvectionOutput,
    polynomialTensorCubeCoefficients_multiplyFirst,
    polynomialTensorCubeCoefficients_multiplySecond,
    polynomialTensorCubeCoefficients_multiplyFirstSecond] using h

/-- Diagonal action of the actual special-linear transvection on the tensor cube. -/
noncomputable def polynomialSLTensorCubeAction
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ) :
    PolynomialVectorTensorCube F →ₗ[F] PolynomialVectorTensorCube F :=
  TensorProduct.map
    (Matrix.SpecialLinearGroup.toLin'
      (polynomialSLTransvection F target source hts n)).toLinearMap <|
      TensorProduct.map
        (Matrix.SpecialLinearGroup.toLin'
          (polynomialSLTransvection F target source hts n)).toLinearMap
        (Matrix.SpecialLinearGroup.toLin'
          (polynomialSLTransvection F target source hts n)).toLinearMap

/-- The actual `SL₃(F[t])` tensor action equals the explicit transvection action. -/
theorem polynomialSLTensorCubeAction_eq
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ) :
    polynomialSLTensorCubeAction F target source hts n =
      polynomialTensorCubeTransvection F target source n := by
  rw [polynomialSLTensorCubeAction, polynomialTensorCubeTransvection]
  rw [polynomialSLTransvection_toLinearMap]

/-- Final coordinate formula for the actual special-linear tensor action. -/
theorem polynomialSLTensorCubeAction_coords
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ)
    (w : PolynomialVectorTensorCube F)
    (a b c : Fin 3) (hc : c ≠ target) :
    polynomialVectorTensorCubeCoords F
        (polynomialSLTensorCubeAction F target source hts n w) a b c =
      firstTwoTransvectionOutput target source n
        (polynomialVectorTensorCubeCoords F w) a b c := by
  rw [polynomialSLTensorCubeAction_eq]
  exact polynomialTensorCubeTransvection_coords
    F target source n w a b c hc

end LeanMathlib.Rigidity
