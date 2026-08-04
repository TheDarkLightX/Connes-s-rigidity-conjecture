import Mathlib
import LeanMathlib.Rigidity.AbelianCocycleExtensionEquiv
import LeanMathlib.Rigidity.PolynomialVectorShear

namespace LeanMathlib.Rigidity

/-- Tensor-cube maps compose as expected. -/
theorem tensorCubeMap_comp
    (L M : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    (w : PolynomialVectorTensorCube (ZMod 3)) :
    tensorCubeMap L (tensorCubeMap M w) =
      tensorCubeMap (L.comp M) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul u q =>
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul v z => simp [tensorCubeMap]

/-- The tensor-cube map of the identity is the identity. -/
theorem tensorCubeMap_id
    (w : PolynomialVectorTensorCube (ZMod 3)) :
    tensorCubeMap LinearMap.id w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul u q =>
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul v z => simp [tensorCubeMap]

/-- Pullback by a linear equivalence on the polynomial-vector dual. -/
noncomputable def polynomialVectorDualPullbackEquiv
    (L : PolynomialVector3 (ZMod 3) ≃ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) :
    PolynomialVectorDual ≃ₗ[ZMod 3] PolynomialVectorDual where
  toLinearMap := polynomialVectorDualPrecompose L.symm.toLinearMap
  invFun := polynomialVectorDualPrecompose L.toLinearMap
  left_inv := by
    intro ell
    ext v
    simp
  right_inv := by
    intro ell
    ext v
    simp

/-- The tensor action of a linear equivalence on divided cubes. -/
noncomputable def dividedCubeMapEquiv
    (L : PolynomialVector3 (ZMod 3) ≃ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) :
    dividedCubeSubmodule (ZMod 3) ≃ₗ[ZMod 3]
      dividedCubeSubmodule (ZMod 3) where
  toLinearMap := dividedCubeMap L.toLinearMap
  invFun := dividedCubeMap L.symm.toLinearMap
  left_inv := by
    intro w
    apply Subtype.ext
    change tensorCubeMap L.symm.toLinearMap
        (tensorCubeMap L.toLinearMap w) = w
    rw [tensorCubeMap_comp]
    have hcomp : L.symm.toLinearMap.comp L.toLinearMap = LinearMap.id := by
      ext v
      simp
    rw [hcomp, tensorCubeMap_id]
  right_inv := by
    intro w
    apply Subtype.ext
    change tensorCubeMap L.toLinearMap
        (tensorCubeMap L.symm.toLinearMap w) = w
    rw [tensorCubeMap_comp]
    have hcomp : L.toLinearMap.comp L.symm.toLinearMap = LinearMap.id := by
      ext v
      simp
    rw [hcomp, tensorCubeMap_id]

/-- Pullback by a linear equivalence on the divided-cube dual. -/
noncomputable def dividedCubeDualPullbackEquiv
    (L : PolynomialVector3 (ZMod 3) ≃ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) :
    DividedCubeDual ≃ₗ[ZMod 3] DividedCubeDual where
  toLinearMap := dividedCubeDualPrecompose L.symm.toLinearMap
  invFun := dividedCubeDualPrecompose L.toLinearMap
  left_inv := by
    intro q
    ext w
    simp only [dividedCubeDualPrecompose_apply]
    have h := (dividedCubeMapEquiv L).symm_apply_apply w
    exact congrArg q h
  right_inv := by
    intro q
    ext w
    simp only [dividedCubeDualPrecompose_apply]
    have h := (dividedCubeMapEquiv L).apply_symm_apply w
    exact congrArg q h

/-- Shifted carry compatibility for a shift-commuting linear equivalence. -/
theorem ternaryShiftedCarry_pullback_compatible
    (L : PolynomialVector3 (ZMod 3) ≃ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    (n : ℕ)
    (hcomm : CommutesWithPolynomialShift L.symm.toLinearMap n) :
    (ternaryShiftedFunctionalCarryCocycle n).AutomorphismCompatible
      (polynomialVectorDualPullbackEquiv L).toAddEquiv
      (dividedCubeDualPullbackEquiv L).toAddEquiv := by
  intro ell m
  exact (ternaryShiftedFunctionalCarry_natural
    L.symm.toLinearMap n hcomm ell m).symm

/-- Every invertible polynomial shear acts on every shifted carry extension. -/
noncomputable def ternaryShiftedCarryShearAction
    (n : ℕ) (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3)) :
    TernaryShiftedCarryExtension n ≃+
      TernaryShiftedCarryExtension n :=
  let L := polynomialVectorShearEquiv target source hts q
  (ternaryShiftedFunctionalCarryCocycle n).extensionAddEquiv
    (polynomialVectorDualPullbackEquiv L).toAddEquiv
    (dividedCubeDualPullbackEquiv L).toAddEquiv
    (ternaryShiftedCarry_pullback_compatible L n
      (by
        simpa [polynomialVectorShearEquiv_symm_apply] using
          polynomialVectorShear_commutes_shift target source (-q) n))

@[simp]
theorem ternaryShiftedCarryShearAction_base
    (n : ℕ) (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3))
    (x : TernaryShiftedCarryExtension n) :
    (ternaryShiftedCarryShearAction n target source hts q x).base =
      polynomialVectorDualPullbackEquiv
        (polynomialVectorShearEquiv target source hts q) x.base := rfl

@[simp]
theorem ternaryShiftedCarryShearAction_fiber
    (n : ℕ) (target source : Fin 3) (hts : target ≠ source)
    (q : Polynomial (ZMod 3))
    (x : TernaryShiftedCarryExtension n) :
    (ternaryShiftedCarryShearAction n target source hts q x).fiber =
      dividedCubeDualPullbackEquiv
        (polynomialVectorShearEquiv target source hts q) x.fiber := rfl

end LeanMathlib.Rigidity
