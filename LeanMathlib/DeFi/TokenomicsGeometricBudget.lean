import LeanMathlib.DeFi.TokenomicsSupply
import Mathlib.Algebra.Ring.GeomSum

open Finset

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Per-step exact discounted burn stream for a fixed contraction factor. -/
def discountedBurn (initial q : Rat) (i : Nat) : Rat :=
  initial * ((1 - q) * q ^ i)

/-- Cumulative exact discounted burn over the first `n` steps. -/
def cumulativeDiscountedBurn (initial q : Rat) (n : Nat) : Rat :=
  ∑ i ∈ Finset.range n, discountedBurn initial q i

theorem discountedMass_eq_one_sub_pow (q : Rat) (n : Nat) :
    (∑ i ∈ Finset.range n, q ^ i) * (1 - q) = 1 - q ^ n := by
  simpa using geom_sum_mul_neg (x := q) n

theorem cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow
    (initial q : Rat) (n : Nat) :
    cumulativeDiscountedBurn initial q n = initial * (1 - q ^ n) := by
  unfold cumulativeDiscountedBurn discountedBurn
  calc
    (∑ i ∈ Finset.range n, initial * ((1 - q) * q ^ i))
        = initial * (∑ i ∈ Finset.range n, (1 - q) * q ^ i) := by
            rw [Finset.mul_sum]
    _ = initial * ((1 - q) * ∑ i ∈ Finset.range n, q ^ i) := by
            congr 1
            rw [Finset.mul_sum]
    _ = initial * (1 - q ^ n) := by
            rw [mul_neg_geom_sum]

theorem residualSupply_after_cumulativeDiscountedBurn
    (initial q : Rat) (n : Nat) :
    initial - cumulativeDiscountedBurn initial q n = initial * q ^ n := by
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  ring

theorem cumulativeDiscountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    0 ≤ cumulativeDiscountedBurn initial q n := by
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  exact mul_nonneg hInitial (sub_nonneg.mpr (factor_pow_le_one hqNonneg hqLeOne n))

theorem cumulativeDiscountedBurn_le_initial
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeDiscountedBurn initial q n ≤ initial := by
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  have hPowNonneg : 0 ≤ q ^ n := pow_nonneg hqNonneg n
  have hMassLe : 1 - q ^ n ≤ 1 := by linarith
  calc
    initial * (1 - q ^ n) ≤ initial * 1 :=
      mul_le_mul_of_nonneg_left hMassLe hInitial
    _ = initial := by ring

theorem residualSupply_after_cumulativeDiscountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hInitial : 0 ≤ initial) (n : Nat) :
    0 ≤ initial - cumulativeDiscountedBurn initial q n := by
  rw [residualSupply_after_cumulativeDiscountedBurn]
  exact mul_nonneg hInitial (pow_nonneg hqNonneg n)

theorem cumulativeDiscountedBurn_lt_initial_of_pos_factor
    {initial q : Rat}
    (hqPos : 0 < q) (hInitial : 0 < initial) (n : Nat) :
    cumulativeDiscountedBurn initial q n < initial := by
  have hResidual : 0 < initial * q ^ n := mul_pos hInitial (pow_pos hqPos n)
  have hEq := residualSupply_after_cumulativeDiscountedBurn initial q n
  linarith

theorem cumulativeDiscountedBurn_succ
    (initial q : Rat) (n : Nat) :
    cumulativeDiscountedBurn initial q (n + 1) =
      cumulativeDiscountedBurn initial q n + discountedBurn initial q n := by
  unfold cumulativeDiscountedBurn
  simp [Finset.sum_range_succ]

theorem cumulativeDiscountedBurn_mono_succ
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeDiscountedBurn initial q n ≤ cumulativeDiscountedBurn initial q (n + 1) := by
  rw [cumulativeDiscountedBurn_succ]
  have hOneSub : 0 ≤ 1 - q := sub_nonneg.mpr hqLeOne
  have hBurnNonneg : 0 ≤ discountedBurn initial q n := by
    unfold discountedBurn
    exact mul_nonneg hInitial (mul_nonneg hOneSub (pow_nonneg hqNonneg n))
  linarith

end MarketSystem

end DeFi

end LeanMathlib
