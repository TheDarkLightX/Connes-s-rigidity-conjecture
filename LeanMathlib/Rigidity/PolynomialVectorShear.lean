import Mathlib
import LeanMathlib.Rigidity.TernaryCarryNaturality

namespace LeanMathlib.Rigidity

/-- Polynomial elementary shear with arbitrary polynomial coefficient. -/
noncomputable def polynomialVectorShear
    (target source : Fin 3) (q : Polynomial (ZMod 3)) :
    PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3) where
  toFun v i := v i + if i = target then q * v source else 0
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
theorem polynomialVectorShear_apply
    (target source : Fin 3) (q : Polynomial (ZMod 3))
    (v : PolynomialVector3 (ZMod 3)) (i : Fin 3) :
    polynomialVectorShear target source q v i =
      v i + if i = target then q * v source else 0 := rfl

/-- A shear leaves its source coordinate unchanged when target and source differ. -/
@[simp]
theorem polynomialVectorShear_source
    (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3))
    (v : PolynomialVector3 (ZMod 3)) :
    polynomialVectorShear target source q v source = v source := by
  simp [polynomialVectorShear, Ne.symm hts]

/-- A shear is inverted by the shear with negative coefficient. -/
noncomputable def polynomialVectorShearEquiv
    (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3)) :
    PolynomialVector3 (ZMod 3) ≃ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3) where
  toLinearMap := polynomialVectorShear target source q
  invFun := polynomialVectorShear target source (-q)
  left_inv := by
    intro v
    funext i
    by_cases hi : i = target
    · subst i
      simp [polynomialVectorShear, hts, Ne.symm hts]
    · simp [polynomialVectorShear, hi]
  right_inv := by
    intro v
    funext i
    by_cases hi : i = target
    · subst i
      simp [polynomialVectorShear, hts, Ne.symm hts]
    · simp [polynomialVectorShear, hi]

@[simp]
theorem polynomialVectorShearEquiv_apply
    (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3))
    (v : PolynomialVector3 (ZMod 3)) :
    polynomialVectorShearEquiv target source hts q v =
      polynomialVectorShear target source q v := rfl

@[simp]
theorem polynomialVectorShearEquiv_symm_apply
    (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3))
    (v : PolynomialVector3 (ZMod 3)) :
    (polynomialVectorShearEquiv target source hts q).symm v =
      polynomialVectorShear target source (-q) v := rfl

/-- Every polynomial shear commutes with every scalar polynomial shift. -/
theorem polynomialVectorShear_commutes_shift
    (target source : Fin 3) (q : Polynomial (ZMod 3)) (n : ℕ) :
    CommutesWithPolynomialShift
      (polynomialVectorShear target source q) n := by
  apply LinearMap.ext
  intro v
  funext i
  by_cases hi : i = target
  · subst i
    simp [CommutesWithPolynomialShift, polynomialVectorShear,
      polynomialVectorShift]
    ring
  · simp [CommutesWithPolynomialShift, polynomialVectorShear,
      polynomialVectorShift, hi]

/-- The monomial transvection is the corresponding arbitrary-coefficient shear. -/
theorem polynomialVectorTransvection_eq_shear
    (target source : Fin 3) (n : ℕ) :
    polynomialVectorTransvection (ZMod 3) target source n =
      polynomialVectorShear target source
        ((Polynomial.X : Polynomial (ZMod 3)) ^ n) := by
  rfl

end LeanMathlib.Rigidity
