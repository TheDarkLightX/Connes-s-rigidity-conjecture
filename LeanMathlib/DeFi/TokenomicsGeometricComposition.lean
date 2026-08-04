import LeanMathlib.DeFi.TokenomicsGeometricBudget

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

theorem discountedBurn_tail (initial q : Rat) (m i : Nat) :
    discountedBurn initial q (m + i) =
      discountedBurn (initial * q ^ m) q i := by
  unfold discountedBurn
  rw [pow_add]
  ring

theorem cumulativeDiscountedBurn_split (initial q : Rat) (m n : Nat) :
    cumulativeDiscountedBurn initial q (m + n) =
      cumulativeDiscountedBurn initial q m +
        cumulativeDiscountedBurn (initial * q ^ m) q n := by
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  rw [cumulativeDiscountedBurn_eq_initial_mul_one_sub_pow]
  rw [pow_add]
  ring

theorem residualSupply_after_cumulativeDiscountedBurn_split
    (initial q : Rat) (m n : Nat) :
    initial - cumulativeDiscountedBurn initial q (m + n) =
      (initial * q ^ m) -
        cumulativeDiscountedBurn (initial * q ^ m) q n := by
  rw [residualSupply_after_cumulativeDiscountedBurn]
  rw [residualSupply_after_cumulativeDiscountedBurn]
  rw [pow_add]
  ring

theorem cumulativeDiscountedBurn_tail_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    0 ≤ cumulativeDiscountedBurn (initial * q ^ m) q n := by
  have hTailInitial : 0 ≤ initial * q ^ m :=
    mul_nonneg hInitial (pow_nonneg hqNonneg m)
  exact cumulativeDiscountedBurn_nonneg hqNonneg hqLeOne hTailInitial n

theorem cumulativeDiscountedBurn_le_add_horizon
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    cumulativeDiscountedBurn initial q m ≤
      cumulativeDiscountedBurn initial q (m + n) := by
  rw [cumulativeDiscountedBurn_split]
  exact le_add_of_nonneg_right
    (cumulativeDiscountedBurn_tail_nonneg hqNonneg hqLeOne hInitial m n)

theorem residualSupply_after_cumulativeDiscountedBurn_add_le
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    initial - cumulativeDiscountedBurn initial q (m + n) ≤
      initial - cumulativeDiscountedBurn initial q m := by
  rw [residualSupply_after_cumulativeDiscountedBurn]
  rw [residualSupply_after_cumulativeDiscountedBurn]
  have hTailInitial : 0 ≤ initial * q ^ m :=
    mul_nonneg hInitial (pow_nonneg hqNonneg m)
  have hTailBound :=
    factor_pow_mul_le_initial hqNonneg hqLeOne hTailInitial n
  rw [pow_add]
  calc
    initial * (q ^ m * q ^ n) = q ^ n * (initial * q ^ m) := by ring
    _ ≤ initial * q ^ m := hTailBound

end MarketSystem

end DeFi

end LeanMathlib
