import LeanMathlib.DeFi.TokenomicsGeometricBudget

open Finset

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Time-weighted discounted burn term. -/
def timeWeightedDiscountedBurn (initial q : Rat) (i : Nat) : Rat :=
  (i : Rat) * discountedBurn initial q i

/-- First moment of the discounted burn stream through horizon `n`. -/
def cumulativeTimeWeightedDiscountedBurn (initial q : Rat) (n : Nat) : Rat :=
  ∑ i ∈ Finset.range n, timeWeightedDiscountedBurn initial q i

/-- Average burn time, defined when cumulative discounted burn is positive. -/
def averageDiscountedBurnTime (initial q : Rat) (n : Nat) : Rat :=
  cumulativeTimeWeightedDiscountedBurn initial q n /
    cumulativeDiscountedBurn initial q n

theorem discountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (i : Nat) :
    0 ≤ discountedBurn initial q i := by
  unfold discountedBurn
  have hOneSub : 0 ≤ 1 - q := sub_nonneg.mpr hqLeOne
  exact mul_nonneg hInitial (mul_nonneg hOneSub (pow_nonneg hqNonneg i))

theorem cumulativeDiscountedBurn_pos
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) (hInitial : 0 < initial) {n : Nat}
    (hn : n ≠ 0) :
    0 < cumulativeDiscountedBurn initial q n := by
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  have hPowLt : q ^ n < 1 := pow_lt_one₀ hqNonneg hqLtOne hn
  exact mul_pos hInitial (sub_pos.mpr hPowLt)

theorem timeWeightedDiscountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (i : Nat) :
    0 ≤ timeWeightedDiscountedBurn initial q i := by
  unfold timeWeightedDiscountedBurn
  exact mul_nonneg (by exact_mod_cast Nat.zero_le i)
    (discountedBurn_nonneg hqNonneg hqLeOne hInitial i)

theorem cumulativeTimeWeightedDiscountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    0 ≤ cumulativeTimeWeightedDiscountedBurn initial q n := by
  unfold cumulativeTimeWeightedDiscountedBurn
  exact Finset.sum_nonneg fun i _ =>
    timeWeightedDiscountedBurn_nonneg hqNonneg hqLeOne hInitial i

theorem cumulativeTimeWeightedDiscountedBurn_le_horizon_mul_cumulativeBurn
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q n ≤
      (n : Rat) * cumulativeDiscountedBurn initial q n := by
  unfold cumulativeTimeWeightedDiscountedBurn timeWeightedDiscountedBurn cumulativeDiscountedBurn
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    have hIndex : (i : Rat) ≤ n := by
      exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hi)
    exact mul_le_mul_of_nonneg_right hIndex
      (discountedBurn_nonneg hqNonneg hqLeOne hInitial i)

theorem cumulativeTimeWeightedDiscountedBurn_le_horizon_mul_initial
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q n ≤ (n : Rat) * initial := by
  have hMoment :=
    cumulativeTimeWeightedDiscountedBurn_le_horizon_mul_cumulativeBurn
      hqNonneg hqLeOne hInitial n
  have hBudget := cumulativeDiscountedBurn_le_initial hqNonneg hInitial n
  have hHorizonNonneg : 0 ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
  exact hMoment.trans (mul_le_mul_of_nonneg_left hBudget hHorizonNonneg)

theorem timeWeightedResidualBudget_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    0 ≤ (n : Rat) * initial - cumulativeTimeWeightedDiscountedBurn initial q n := by
  exact sub_nonneg.mpr
    (cumulativeTimeWeightedDiscountedBurn_le_horizon_mul_initial
      hqNonneg hqLeOne hInitial n)

theorem averageDiscountedBurnTime_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) {n : Nat}
    (hPositiveMass : 0 < cumulativeDiscountedBurn initial q n) :
    0 ≤ averageDiscountedBurnTime initial q n := by
  unfold averageDiscountedBurnTime
  exact div_nonneg
    (cumulativeTimeWeightedDiscountedBurn_nonneg hqNonneg hqLeOne hInitial n)
    hPositiveMass.le

theorem averageDiscountedBurnTime_le_horizon
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) {n : Nat}
    (hPositiveMass : 0 < cumulativeDiscountedBurn initial q n) :
    averageDiscountedBurnTime initial q n ≤ n := by
  unfold averageDiscountedBurnTime
  rw [div_le_iff₀ hPositiveMass]
  exact cumulativeTimeWeightedDiscountedBurn_le_horizon_mul_cumulativeBurn
    hqNonneg hqLeOne hInitial n

theorem averageDiscountedBurnTime_between_zero_and_horizon_of_strict_factor
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) (hInitial : 0 < initial) {n : Nat}
    (hn : n ≠ 0) :
    0 ≤ averageDiscountedBurnTime initial q n ∧
      averageDiscountedBurnTime initial q n ≤ n := by
  have hMass := cumulativeDiscountedBurn_pos hqNonneg hqLtOne hInitial hn
  exact ⟨
    averageDiscountedBurnTime_nonneg hqNonneg hqLtOne.le hInitial.le hMass,
    averageDiscountedBurnTime_le_horizon hqNonneg hqLtOne.le hInitial.le hMass⟩

theorem cumulativeTimeWeightedDiscountedBurn_succ
    (initial q : Rat) (n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q (n + 1) =
      cumulativeTimeWeightedDiscountedBurn initial q n +
        timeWeightedDiscountedBurn initial q n := by
  unfold cumulativeTimeWeightedDiscountedBurn
  simp [Finset.sum_range_succ]

theorem cumulativeTimeWeightedDiscountedBurn_mono_succ
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q n ≤
      cumulativeTimeWeightedDiscountedBurn initial q (n + 1) := by
  rw [cumulativeTimeWeightedDiscountedBurn_succ]
  have hStepNonneg := timeWeightedDiscountedBurn_nonneg hqNonneg hqLeOne hInitial n
  linarith

end MarketSystem

end DeFi

end LeanMathlib
