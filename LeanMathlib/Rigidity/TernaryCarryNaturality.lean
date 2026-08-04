import Mathlib
import LeanMathlib.Rigidity.TernaryShiftedCarry
import LeanMathlib.Rigidity.TernaryFrobeniusNaturality

namespace LeanMathlib.Rigidity

/-- Pull back a polynomial-vector functional along a linear map. -/
noncomputable def polynomialVectorDualPrecompose
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) :
    PolynomialVectorDual →ₗ[ZMod 3] PolynomialVectorDual where
  toFun ell := ell.comp L
  map_add' := by
    intro ell m
    ext v
    simp
  map_smul' := by
    intro c ell
    ext v
    simp

@[simp]
theorem polynomialVectorDualPrecompose_apply
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    (ell : PolynomialVectorDual)
    (v : PolynomialVector3 (ZMod 3)) :
    polynomialVectorDualPrecompose L ell v = ell (L v) := rfl

/-- Restriction of the diagonal tensor action to the divided-cube submodule. -/
noncomputable def dividedCubeMap
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) :
    dividedCubeSubmodule (ZMod 3) →ₗ[ZMod 3]
      dividedCubeSubmodule (ZMod 3) where
  toFun w := ⟨tensorCubeMap L w.1,
    tensorCubeMap_mem_dividedCube L w.2⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp

@[simp]
theorem dividedCubeMap_coe
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    (w : dividedCubeSubmodule (ZMod 3)) :
    ((dividedCubeMap L w : dividedCubeSubmodule (ZMod 3)) :
      PolynomialVectorTensorCube (ZMod 3)) = tensorCubeMap L w := rfl

/-- Pull back a divided-cube functional along the tensor action. -/
noncomputable def dividedCubeDualPrecompose
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) :
    DividedCubeDual →ₗ[ZMod 3] DividedCubeDual where
  toFun q := q.comp (dividedCubeMap L)
  map_add' := by
    intro q r
    ext w
    simp
  map_smul' := by
    intro c q
    ext w
    simp

@[simp]
theorem dividedCubeDualPrecompose_apply
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    (q : DividedCubeDual)
    (w : dividedCubeSubmodule (ZMod 3)) :
    dividedCubeDualPrecompose L q w = q (dividedCubeMap L w) := rfl

/-- Naturality of ternary carry under arbitrary linear maps. -/
theorem ternaryFunctionalCarry_natural
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    (ell m : PolynomialVectorDual) :
    ternaryFunctionalCarry
        (polynomialVectorDualPrecompose L ell)
        (polynomialVectorDualPrecompose L m) =
      dividedCubeDualPrecompose L (ternaryFunctionalCarry ell m) := by
  ext w
  rcases w with ⟨b, hb⟩
  change
    ternaryCarryTensorFunctional
      (polynomialVectorDualPrecompose L ell)
      (polynomialVectorDualPrecompose L m) b =
    ternaryCarryTensorFunctional ell m (tensorCubeMap L b)
  refine Submodule.span_induction
    (p := fun x _ =>
      ternaryCarryTensorFunctional
          (polynomialVectorDualPrecompose L ell)
          (polynomialVectorDualPrecompose L m) x =
        ternaryCarryTensorFunctional ell m (tensorCubeMap L x))
    ?_ ?_ ?_ ?_ hb
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp [tensorCubeMap_pureCube]
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro c x hx
    simp [map_smul, hx]

/-- A linear map commutes with the degree shift `t^n`. -/
def CommutesWithPolynomialShift
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) (n : ℕ) : Prop :=
  L.comp (polynomialVectorShift n) =
    (polynomialVectorShift n).comp L

/-- Pullback along a shift-commuting map commutes with dual shift. -/
theorem dualPrecompose_commutes_dualShift
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) (n : ℕ)
    (hcomm : CommutesWithPolynomialShift L n)
    (ell : PolynomialVectorDual) :
    polynomialVectorDualPrecompose L
        (polynomialVectorDualShift n ell) =
      polynomialVectorDualShift n
        (polynomialVectorDualPrecompose L ell) := by
  ext v
  have hv := LinearMap.congr_fun hcomm v
  simp [CommutesWithPolynomialShift] at hv
  simpa using (congrArg ell hv).symm

/-- Naturality of shifted carry under shift-commuting linear maps. -/
theorem ternaryShiftedFunctionalCarry_natural
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3)) (n : ℕ)
    (hcomm : CommutesWithPolynomialShift L n)
    (ell m : PolynomialVectorDual) :
    ternaryShiftedFunctionalCarry n
        (polynomialVectorDualPrecompose L ell)
        (polynomialVectorDualPrecompose L m) =
      dividedCubeDualPrecompose L
        (ternaryShiftedFunctionalCarry n ell m) := by
  simp only [ternaryShiftedFunctionalCarry]
  rw [← dualPrecompose_commutes_dualShift L n hcomm ell,
    ← dualPrecompose_commutes_dualShift L n hcomm m]
  exact ternaryFunctionalCarry_natural L _ _

end LeanMathlib.Rigidity
