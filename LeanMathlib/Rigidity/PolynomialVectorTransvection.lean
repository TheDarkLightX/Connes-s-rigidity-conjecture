import Mathlib
import LeanMathlib.Rigidity.PolynomialVectorTensorCubeCoords

namespace LeanMathlib.Rigidity

open Matrix

/-- Explicit rank-three polynomial transvection on column vectors. -/
noncomputable def polynomialVectorTransvection
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ) :
    PolynomialVector3 F →ₗ[F] PolynomialVector3 F where
  toFun v i :=
    v i + if i = target then (Polynomial.X : Polynomial F) ^ n * v source else 0
  map_add' := by
    intro u v
    funext i
    by_cases hi : i = target <;>
      simp [hi, mul_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c v
    funext i
    by_cases hi : i = target <;>
      simp [hi, mul_assoc, mul_left_comm, mul_comm, add_assoc]

@[simp]
theorem polynomialVectorTransvection_apply
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (v : PolynomialVector3 F) (i : Fin 3) :
    polynomialVectorTransvection F target source n v i =
      v i + if i = target then (Polynomial.X : Polynomial F) ^ n * v source else 0 :=
  rfl

/-- The actual elementary matrix in `SL₃(F[t])`. -/
noncomputable def polynomialSLTransvection
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin 3) (Polynomial F) :=
  ⟨Matrix.transvection target source ((Polynomial.X : Polynomial F) ^ n),
    Matrix.det_transvection_of_ne target source hts _⟩

@[simp]
theorem polynomialSLTransvection_coe
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ) :
    ((polynomialSLTransvection F target source hts n :
      Matrix.SpecialLinearGroup (Fin 3) (Polynomial F)) :
      Matrix (Fin 3) (Fin 3) (Polynomial F)) =
      Matrix.transvection target source ((Polynomial.X : Polynomial F) ^ n) :=
  rfl

/-- Matrix multiplication by a transvection gives the explicit coordinate update. -/
theorem transvection_mulVec_apply
    (F : Type*) [Field F]
    (target source : Fin 3) (n : ℕ)
    (v : PolynomialVector3 F) (i : Fin 3) :
    (Matrix.transvection target source ((Polynomial.X : Polynomial F) ^ n) *ᵥ v) i =
      polynomialVectorTransvection F target source n v i := by
  classical
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  by_cases hi : i = target
  · subst i
    simp [polynomialVectorTransvection]
  · simp [polynomialVectorTransvection, hi]

/-- Mathlib's actual `SL₃` representation agrees with the explicit transvection map. -/
theorem polynomialSLTransvection_toLin_apply
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ)
    (v : PolynomialVector3 F) (i : Fin 3) :
    Matrix.SpecialLinearGroup.toLin'
        (polynomialSLTransvection F target source hts n) v i =
      polynomialVectorTransvection F target source n v i := by
  change
    (Matrix.transvection target source ((Polynomial.X : Polynomial F) ^ n) *ᵥ v) i = _
  exact transvection_mulVec_apply F target source n v i

/-- The special-linear transvection action, restricted from `F[t]` scalars to `F`. -/
noncomputable def polynomialSLTransvectionLinearMap
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ) :
    PolynomialVector3 F →ₗ[F] PolynomialVector3 F :=
  (Matrix.SpecialLinearGroup.toLin'
    (polynomialSLTransvection F target source hts n)).toLinearMap.restrictScalars F

/-- Equality of the actual `SL₃` linear action and the explicit update map. -/
theorem polynomialSLTransvection_toLinearMap
    (F : Type*) [Field F]
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ) :
    polynomialSLTransvectionLinearMap F target source hts n =
      polynomialVectorTransvection F target source n := by
  apply LinearMap.ext
  intro v
  funext i
  exact polynomialSLTransvection_toLin_apply F target source hts n v i

end LeanMathlib.Rigidity
