import Mathlib

namespace LeanMathlib.Rigidity

open scoped BigOperators

/-- A finite weighted average is bounded above by one of its entries. -/
theorem exists_ge_weighted_average
    {ι : Type*} [Finite ι] [Nonempty ι]
    (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ∃ i, (∑ j, w j * x j) ≤ x i := by
  classical
  obtain ⟨i, hi⟩ := Finite.exists_max x
  refine ⟨i, ?_⟩
  calc
    (∑ j, w j * x j) ≤ ∑ j, w j * x i := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi j) (hw j)
    _ = (∑ j, w j) * x i := by rw [Finset.sum_mul]
    _ = x i := by rw [hsum, one_mul]

/-- The correlation term controlling coefficient-level Hopf defect. -/
def coefficientHopfCorrelation
    {ι : Type*} [Fintype ι] (a : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (a i) * (a i).re

/-- The squared defect predicted by the diagonal-coproduct Fourier calculation. -/
def coefficientHopfDefectSq
    {ι : Type*} [Fintype ι] (a : ι → ℂ) : ℝ :=
  2 - 2 * coefficientHopfCorrelation a

/--
For an `ℓ²`-normalized finite coefficient vector, some coefficient has real
part at least the Hopf correlation. This is the finite weighted-average core
of the approximate group-like rounding lemma.
-/
theorem exists_re_ge_hopfCorrelation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℂ)
    (hnorm : ∑ i, Complex.normSq (a i) = 1) :
    ∃ i, coefficientHopfCorrelation a ≤ (a i).re := by
  simpa [coefficientHopfCorrelation] using
    exists_ge_weighted_average
      (fun i => Complex.normSq (a i))
      (fun i => (a i).re)
      (fun i => Complex.normSq_nonneg (a i)) hnorm

/--
Coefficient-level quantitative rounding estimate. The left side is the
squared `ℓ²` distance expression to a basis vector after expanding the norm;
the right side is the squared Hopf defect expression.
-/
theorem exists_rounding_bound_from_hopfCorrelation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℂ)
    (hnorm : ∑ i, Complex.normSq (a i) = 1) :
    ∃ i, 2 - 2 * (a i).re ≤ coefficientHopfDefectSq a := by
  obtain ⟨i, hi⟩ := exists_re_ge_hopfCorrelation a hnorm
  refine ⟨i, ?_⟩
  simp [coefficientHopfDefectSq]
  linarith

/-- Elementary complex identity used to convert the real-part bound to distance. -/
theorem normSq_sub_one (z : ℂ) :
    Complex.normSq (z - 1) = Complex.normSq z - 2 * z.re + 1 := by
  simp [Complex.normSq_apply]
  ring

/--
For a normalized finite coefficient vector, the squared distance to the basis
vector at `i` is exactly `2 - 2 Re(aᵢ)`.
-/
theorem coefficient_distance_to_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ)
    (hnorm : ∑ j, Complex.normSq (a j) = 1)
    (i : ι) :
    Complex.normSq (a i - 1) +
        ∑ j ∈ (Finset.univ.erase i), Complex.normSq (a j) =
      2 - 2 * (a i).re := by
  have hsplit :
      Complex.normSq (a i) +
          ∑ j ∈ (Finset.univ.erase i), Complex.normSq (a j) = 1 := by
    simpa [Finset.sum_erase_add _ (Finset.mem_univ i)] using hnorm
  rw [normSq_sub_one]
  linarith

/-- Finite-dimensional approximate group-like elements round to a basis vector. -/
theorem finite_approximate_groupLike_rounding
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (a : ι → ℂ)
    (hnorm : ∑ j, Complex.normSq (a j) = 1) :
    ∃ i,
      Complex.normSq (a i - 1) +
          ∑ j ∈ (Finset.univ.erase i), Complex.normSq (a j) ≤
        coefficientHopfDefectSq a := by
  obtain ⟨i, hi⟩ := exists_rounding_bound_from_hopfCorrelation a hnorm
  refine ⟨i, ?_⟩
  rw [coefficient_distance_to_basis a hnorm i]
  exact hi

end LeanMathlib.Rigidity
