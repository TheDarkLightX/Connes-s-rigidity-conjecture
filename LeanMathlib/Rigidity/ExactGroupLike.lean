import Mathlib

namespace LeanMathlib.Rigidity

open scoped BigOperators

/-- Coefficients of the diagonal coproduct on a finite group algebra basis. -/
def diagonalCoeffs {G K : Type*} [DecidableEq G] [Zero K]
    (a : G → K) (g h : G) : K :=
  if g = h then a g else 0

/-- Coefficients of the tensor square of a coefficient vector. -/
def tensorSquareCoeffs {G K : Type*} [Mul K]
    (a : G → K) (g h : G) : K :=
  a g * a h

/--
Finite coefficient core of group reconstruction from a Hopf coproduct.

If a coefficient vector has counit one and its diagonal coproduct equals its
tensor square, then it is a delta function at one basis element. This is the
algebraic heart of the statement that the group-like elements of a group
algebra are exactly the original group elements.
-/
theorem exact_groupLike_coefficients
    {G K : Type*} [Fintype G] [DecidableEq G] [Field K]
    (a : G → K)
    (hcounit : ∑ g, a g = 1)
    (hcomul : ∀ g h, diagonalCoeffs a g h = tensorSquareCoeffs a g h) :
    ∃ g, ∀ h, a h = if h = g then 1 else 0 := by
  have hnonzero : ∃ g, a g ≠ 0 := by
    by_contra h
    push Not at h
    have hsumzero : ∑ g, a g = 0 := by simp [h]
    rw [hsumzero] at hcounit
    exact zero_ne_one hcounit
  obtain ⟨g, hg⟩ := hnonzero
  have hdiag := hcomul g g
  simp [diagonalCoeffs, tensorSquareCoeffs] at hdiag
  have hgone : a g = 1 := by
    have hcancel : (1 : K) * a g = a g * a g := by simpa using hdiag
    have hone : (1 : K) = a g := mul_right_cancel₀ hg hcancel
    exact hone.symm
  refine ⟨g, ?_⟩
  intro h
  by_cases hh : h = g
  · subst h
    simp [hgone]
  · have hgh : g ≠ h := by
      intro hEq
      exact hh hEq.symm
    have hoff := hcomul g h
    simp [diagonalCoeffs, tensorSquareCoeffs, hgh, hgone] at hoff
    simp [hh, hoff]

/-- Delta coefficients satisfy the counit and group-like coproduct equations. -/
theorem delta_groupLike_coefficients
    {G K : Type*} [Fintype G] [DecidableEq G] [Field K]
    (g : G) :
    (∑ h, (if h = g then 1 else 0 : K)) = 1 ∧
      ∀ x y,
        diagonalCoeffs (fun h => if h = g then 1 else 0) x y =
          tensorSquareCoeffs (fun h => if h = g then 1 else 0) x y := by
  constructor
  · simp
  · intro x y
    by_cases hxy : x = y <;>
      by_cases hx : x = g <;>
      by_cases hy : y = g <;>
      simp_all [diagonalCoeffs, tensorSquareCoeffs]

/-- Exact finite-dimensional characterization of group-like coefficient vectors. -/
theorem groupLike_coefficients_iff_delta
    {G K : Type*} [Fintype G] [DecidableEq G] [Field K]
    (a : G → K) :
    ((∑ g, a g = 1) ∧
      ∀ g h, diagonalCoeffs a g h = tensorSquareCoeffs a g h) ↔
      ∃ g, ∀ h, a h = if h = g then 1 else 0 := by
  constructor
  · rintro ⟨hcounit, hcomul⟩
    exact exact_groupLike_coefficients a hcounit hcomul
  · rintro ⟨g, hg⟩
    have ha : a = fun h => if h = g then 1 else 0 := funext hg
    rw [ha]
    constructor
    · simp
    · intro x y
      by_cases hxy : x = y <;>
        by_cases hx : x = g <;>
        by_cases hy : y = g <;>
        simp_all [diagonalCoeffs, tensorSquareCoeffs]

end LeanMathlib.Rigidity
