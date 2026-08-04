import Mathlib
import LeanMathlib.Rigidity.PolynomialVectorDualCoordinates
import LeanMathlib.Rigidity.TernaryTruncatedInvariant

namespace LeanMathlib.Rigidity

/-- Extend a finite low-degree coefficient array by zero above degree `n`. -/
def extendLowDegreeCoordinates (n : ℕ) :
    TernaryTruncatedCoefficients n →ₗ[ZMod 3]
      (PolynomialVectorBasisIndex → ZMod 3) where
  toFun g ik := if h : ik.2 < n then g ik.1 ⟨ik.2, h⟩ else 0
  map_add' := by
    intro g h
    funext ik
    by_cases hk : ik.2 < n <;> simp [hk]
  map_smul' := by
    intro c g
    funext ik
    by_cases hk : ik.2 < n <;> simp [hk]

@[simp]
theorem extendLowDegreeCoordinates_apply_lt
    (n : ℕ) (g : TernaryTruncatedCoefficients n)
    (i : Fin 3) (k : ℕ) (hk : k < n) :
    extendLowDegreeCoordinates n g ⟨i, k⟩ = g i ⟨k, hk⟩ := by
  simp [extendLowDegreeCoordinates, hk]

@[simp]
theorem extendLowDegreeCoordinates_apply_ge
    (n : ℕ) (g : TernaryTruncatedCoefficients n)
    (i : Fin 3) (k : ℕ) (hk : n ≤ k) :
    extendLowDegreeCoordinates n g ⟨i, k⟩ = 0 := by
  simp [extendLowDegreeCoordinates, Nat.not_lt.mpr hk]

/-- Zero extension lies in the kernel of coordinate tail shift. -/
theorem extendLowDegreeCoordinates_mem_ker
    (n : ℕ) (g : TernaryTruncatedCoefficients n) :
    extendLowDegreeCoordinates n g ∈
      LinearMap.ker (polynomialDualCoordinateShift n) := by
  funext ik
  rcases ik with ⟨i, k⟩
  simp [polynomialDualCoordinateShift,
    extendLowDegreeCoordinates, Nat.not_lt.mpr (Nat.le_add_right n k)]

/-- A coordinate tail-shift kernel element vanishes in every degree at least `n`. -/
theorem coordinateShiftKernel_eq_zero_of_ge
    (n : ℕ)
    (f : LinearMap.ker (polynomialDualCoordinateShift n))
    (i : Fin 3) (k : ℕ) (hk : n ≤ k) :
    f.1 ⟨i, k⟩ = 0 := by
  let r := k - n
  have hkernel : polynomialDualCoordinateShift n f.1 = 0 := f.property
  have hcoord := congrFun hkernel ⟨i, r⟩
  have hsum : n + r = k := by
    simp [r, Nat.add_sub_of_le hk]
  simpa [polynomialDualCoordinateShift, hsum] using hcoord

/--
The kernel of tail shift consists exactly of arbitrary coefficients in degrees
`0,...,n-1` and zero coefficients thereafter.
-/
noncomputable def coordinateShiftKernelEquiv (n : ℕ) :
    LinearMap.ker (polynomialDualCoordinateShift n) ≃ₗ[ZMod 3]
      TernaryTruncatedCoefficients n where
  toFun f i k := f.1 ⟨i, k.1⟩
  invFun g := ⟨extendLowDegreeCoordinates n g,
    extendLowDegreeCoordinates_mem_ker n g⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext ik
    rcases ik with ⟨i, k⟩
    by_cases hk : k < n
    · simp [hk]
    · have hge : n ≤ k := Nat.le_of_not_gt hk
      simp [extendLowDegreeCoordinates, hk,
        coordinateShiftKernel_eq_zero_of_ge n f i k hge]
  right_inv := by
    intro g
    funext i k
    simp
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- The actual dual-shift kernel is equivalent to the coordinate tail-shift kernel. -/
noncomputable def polynomialVectorDualShiftKernelCoordinateEquiv (n : ℕ) :
    LinearMap.ker (polynomialVectorDualShift n) ≃ₗ[ZMod 3]
      LinearMap.ker (polynomialDualCoordinateShift n) where
  toFun ell := ⟨polynomialVectorDualEquivFun ell.1, by
    change polynomialDualCoordinateShift n
      (polynomialVectorDualEquivFun ell.1) = 0
    rw [← polynomialVectorDualEquivFun_shift, ell.property]
    simp⟩
  invFun f := ⟨polynomialVectorDualEquivFun.symm f.1, by
    apply polynomialVectorDualEquivFun.injective
    rw [polynomialVectorDualEquivFun_shift]
    simpa using f.property⟩
  left_inv := by
    intro ell
    apply Subtype.ext
    simp
  right_inv := by
    intro f
    apply Subtype.ext
    simp
  map_add' := by
    intro ell m
    apply Subtype.ext
    simp
  map_smul' := by
    intro c ell
    apply Subtype.ext
    simp

/-- Actual algebraic dual-shift kernel as the finite low-degree coefficient space. -/
noncomputable def polynomialVectorDualShiftKernelEquiv (n : ℕ) :
    LinearMap.ker (polynomialVectorDualShift n) ≃ₗ[ZMod 3]
      TernaryTruncatedCoefficients n :=
  (polynomialVectorDualShiftKernelCoordinateEquiv n).trans
    (coordinateShiftKernelEquiv n)

noncomputable instance polynomialVectorDualShiftKernelFintype (n : ℕ) :
    Fintype (LinearMap.ker (polynomialVectorDualShift n)) :=
  Fintype.ofEquiv (TernaryTruncatedCoefficients n)
    (polynomialVectorDualShiftKernelEquiv n).symm.toEquiv

/-- Exact cardinality of the shifted algebraic-dual kernel. -/
theorem card_polynomialVectorDualShiftKernel (n : ℕ) :
    Fintype.card (LinearMap.ker (polynomialVectorDualShift n)) =
      3 ^ (3 * n) := by
  rw [Fintype.card_congr (polynomialVectorDualShiftKernelEquiv n).toEquiv]
  simp [TernaryTruncatedCoefficients, Nat.mul_comm, Nat.pow_mul]

end LeanMathlib.Rigidity
