import LeanMathlib.DeFi.TokenomicsWeightedGeometricBudget
import LeanMathlib.DeFi.TokenomicsGeometricComposition

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

theorem timeWeightedDiscountedBurn_tail (initial q : Rat) (m i : Nat) :
    timeWeightedDiscountedBurn initial q (m + i) =
      (m : Rat) * discountedBurn (initial * q ^ m) q i +
        timeWeightedDiscountedBurn (initial * q ^ m) q i := by
  unfold timeWeightedDiscountedBurn discountedBurn
  rw [pow_add]
  norm_num
  ring

theorem cumulativeTimeWeightedDiscountedBurn_split
    (initial q : Rat) (m n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q (m + n) =
      cumulativeTimeWeightedDiscountedBurn initial q m +
        (m : Rat) * cumulativeDiscountedBurn (initial * q ^ m) q n +
          cumulativeTimeWeightedDiscountedBurn (initial * q ^ m) q n := by
  induction n with
  | zero =>
      simp [cumulativeDiscountedBurn, cumulativeTimeWeightedDiscountedBurn]
  | succ n ih =>
      rw [Nat.add_succ]
      rw [cumulativeTimeWeightedDiscountedBurn_succ]
      rw [ih]
      rw [cumulativeDiscountedBurn_succ]
      rw [cumulativeTimeWeightedDiscountedBurn_succ]
      rw [timeWeightedDiscountedBurn_tail]
      ring

theorem cumulativeTimeWeightedDiscountedBurn_tail_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    0 ≤ cumulativeTimeWeightedDiscountedBurn (initial * q ^ m) q n := by
  have hTailInitial : 0 ≤ initial * q ^ m :=
    mul_nonneg hInitial (pow_nonneg hqNonneg m)
  exact cumulativeTimeWeightedDiscountedBurn_nonneg hqNonneg hqLeOne hTailInitial n

theorem cumulativeTimeWeightedDiscountedBurn_le_add_horizon
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    cumulativeTimeWeightedDiscountedBurn initial q m ≤
      cumulativeTimeWeightedDiscountedBurn initial q (m + n) := by
  rw [cumulativeTimeWeightedDiscountedBurn_split]
  have hTailBurn :=
    cumulativeDiscountedBurn_tail_nonneg hqNonneg hqLeOne hInitial m n
  have hTailMoment :=
    cumulativeTimeWeightedDiscountedBurn_tail_nonneg hqNonneg hqLeOne hInitial m n
  have hMNonneg : 0 ≤ (m : Rat) := by exact_mod_cast Nat.zero_le m
  have hOffset :
      0 ≤ (m : Rat) * cumulativeDiscountedBurn (initial * q ^ m) q n :=
    mul_nonneg hMNonneg hTailBurn
  linarith

end MarketSystem

end DeFi

end LeanMathlib
