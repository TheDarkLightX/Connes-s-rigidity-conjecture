import LeanMathlib.DeFi.TokenomicsWeightedGeometricBudget

open Finset

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Finite first moment of the geometric power stream. -/
def weightedPowerSum (q : Rat) (n : Nat) : Rat :=
  ∑ i ∈ Finset.range n, (i : Rat) * q ^ i

/--
Closed-form numerator for the finite first moment of the geometric power stream.

The use of `((n : Rat) - 1)` rather than a natural predecessor keeps the
formula valid at the boundary `n = 0`.
-/
def weightedGeomClosedForm (q : Rat) (n : Nat) : Rat :=
  q - (n : Rat) * q ^ n + ((n : Rat) - 1) * q ^ (n + 1)

theorem cumulativeTimeWeightedDiscountedBurn_eq_initial_mul_one_sub_mul_weightedPowerSum
    (initial q : Rat) (n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q n =
      initial * ((1 - q) * weightedPowerSum q n) := by
  unfold cumulativeTimeWeightedDiscountedBurn timeWeightedDiscountedBurn
  unfold discountedBurn weightedPowerSum
  calc
    (∑ i ∈ Finset.range n, (i : Rat) * (initial * ((1 - q) * q ^ i)))
        = initial * (∑ i ∈ Finset.range n, (1 - q) * ((i : Rat) * q ^ i)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
    _ = initial * ((1 - q) * ∑ i ∈ Finset.range n, (i : Rat) * q ^ i) := by
            congr 1
            rw [Finset.mul_sum]

theorem weightedPowerSum_mul_one_sub_sq (q : Rat) (n : Nat) :
    (1 - q) * ((1 - q) * weightedPowerSum q n) =
      weightedGeomClosedForm q n := by
  induction n with
  | zero =>
      simp [weightedPowerSum, weightedGeomClosedForm]
  | succ n ih =>
      unfold weightedPowerSum at ih ⊢
      unfold weightedGeomClosedForm at ih ⊢
      rw [Finset.sum_range_succ]
      calc
        (1 - q) *
              ((1 - q) *
                (∑ i ∈ Finset.range n, (i : Rat) * q ^ i + (n : Rat) * q ^ n))
            = (1 - q) * ((1 - q) * ∑ i ∈ Finset.range n, (i : Rat) * q ^ i) +
              (1 - q) * ((1 - q) * ((n : Rat) * q ^ n)) := by ring
        _ = (q - (n : Rat) * q ^ n + ((n : Rat) - 1) * q ^ (n + 1)) +
              (1 - q) * ((1 - q) * ((n : Rat) * q ^ n)) := by rw [ih]
        _ = q - ((n + 1 : Nat) : Rat) * q ^ (n + 1) +
              (((n + 1 : Nat) : Rat) - 1) * q ^ ((n + 1) + 1) := by
              norm_num
              ring_nf

theorem cumulativeTimeWeightedDiscountedBurn_closedForm_mul_one_sub
    (initial q : Rat) (n : Nat) :
    (1 - q) * cumulativeTimeWeightedDiscountedBurn initial q n =
      initial * weightedGeomClosedForm q n := by
  rw [cumulativeTimeWeightedDiscountedBurn_eq_initial_mul_one_sub_mul_weightedPowerSum]
  rw [← weightedPowerSum_mul_one_sub_sq q n]
  ring

theorem cumulativeTimeWeightedDiscountedBurn_closedForm
    {initial q : Rat} (hqNeOne : q ≠ 1) (n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q n =
      initial * weightedGeomClosedForm q n / (1 - q) := by
  have hDen : 1 - q ≠ 0 := by
    intro hZero
    apply hqNeOne
    linarith
  rw [eq_div_iff hDen]
  have hEq := cumulativeTimeWeightedDiscountedBurn_closedForm_mul_one_sub initial q n
  linarith

end MarketSystem

end DeFi

end LeanMathlib
