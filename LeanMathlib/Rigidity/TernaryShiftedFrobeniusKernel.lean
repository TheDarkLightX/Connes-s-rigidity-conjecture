import Mathlib
import LeanMathlib.Rigidity.TernaryDualShiftKernel
import LeanMathlib.Rigidity.TernaryShiftedMultiplication

namespace LeanMathlib.Rigidity

/--
Because the divided-cube Frobenius diagonal is surjective, composing a
functional with it is zero exactly when the original functional is zero.
-/
theorem ternaryShiftedFrobeniusDual_eq_zero_iff
    (n : ℕ) (ell : PolynomialVectorDual) :
    ternaryShiftedFrobeniusDual n ell = 0 ↔
      polynomialVectorDualShift n ell = 0 := by
  constructor
  · intro hzero
    apply LinearMap.ext
    intro v
    obtain ⟨w, hwdiv, hdiag⟩ :=
      ternaryFrobeniusDiagonal_dividedCube_surjective v
    let b : dividedCubeSubmodule (ZMod 3) := ⟨w, hwdiv⟩
    have hvalue := DFunLike.congr_fun hzero b
    change ell (polynomialVectorShift n
      (ternaryFrobeniusDiagonal w)) = 0 at hvalue
    change ell (polynomialVectorShift n v) = 0
    simpa [hdiag] using hvalue
  · intro hzero
    ext b
    have hvalue := DFunLike.congr_fun hzero
      (ternaryDividedCubeFrobeniusDiagonal b)
    exact hvalue

/-- Identity-on-functionals equivalence of the two shift kernels. -/
noncomputable def ternaryShiftedFrobeniusKernelEquivDualShift (n : ℕ) :
    LinearMap.ker (ternaryShiftedFrobeniusDual n) ≃ₗ[ZMod 3]
      LinearMap.ker (polynomialVectorDualShift n) where
  toFun ell := ⟨ell.1,
    (ternaryShiftedFrobeniusDual_eq_zero_iff n ell.1).1 ell.property⟩
  invFun ell := ⟨ell.1,
    (ternaryShiftedFrobeniusDual_eq_zero_iff n ell.1).2 ell.property⟩
  left_inv := by intro ell; rfl
  right_inv := by intro ell; rfl
  map_add' := by intro ell m; rfl
  map_smul' := by intro c ell; rfl

/-- Shifted Frobenius-dual kernel as the first `n` coefficient layers. -/
noncomputable def ternaryShiftedFrobeniusKernelEquiv (n : ℕ) :
    LinearMap.ker (ternaryShiftedFrobeniusDual n) ≃ₗ[ZMod 3]
      TernaryTruncatedCoefficients n :=
  (ternaryShiftedFrobeniusKernelEquivDualShift n).trans
    (polynomialVectorDualShiftKernelEquiv n)

noncomputable instance ternaryShiftedFrobeniusKernelFintype (n : ℕ) :
    Fintype (LinearMap.ker (ternaryShiftedFrobeniusDual n)) :=
  Fintype.ofEquiv (TernaryTruncatedCoefficients n)
    (ternaryShiftedFrobeniusKernelEquiv n).symm.toEquiv

/-- Exact intrinsic kernel cardinality at shift `n`. -/
theorem card_ternaryShiftedFrobeniusKernel (n : ℕ) :
    Fintype.card (LinearMap.ker (ternaryShiftedFrobeniusDual n)) =
      3 ^ (3 * n) := by
  rw [Fintype.card_congr (ternaryShiftedFrobeniusKernelEquiv n).toEquiv]
  simp [TernaryTruncatedCoefficients, Fintype.card_fun, Nat.pow_mul]

/-- Distinct shifts have distinct shifted-Frobenius kernel sizes. -/
theorem card_ternaryShiftedFrobeniusKernel_injective :
    Function.Injective
      (fun n : ℕ =>
        Fintype.card (LinearMap.ker (ternaryShiftedFrobeniusDual n))) := by
  intro m n h
  rw [card_ternaryShiftedFrobeniusKernel,
    card_ternaryShiftedFrobeniusKernel] at h
  have hpow : 3 * m = 3 * n := Nat.pow_right_injective (by omega) h
  omega

end LeanMathlib.Rigidity
