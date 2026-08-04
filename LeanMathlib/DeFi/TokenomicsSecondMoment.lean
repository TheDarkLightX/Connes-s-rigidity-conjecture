import LeanMathlib.DeFi.TokenomicsWeightedComposition

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Squared-time weighted discounted burn term. -/
def squaredTimeWeightedDiscountedBurn (initial q : Rat) (i : Nat) : Rat :=
  (i : Rat) ^ 2 * discountedBurn initial q i

/-- Second moment of the discounted burn stream through horizon `n`. -/
def cumulativeSquaredTimeWeightedDiscountedBurn (initial q : Rat) (n : Nat) : Rat :=
  ∑ i ∈ Finset.range n, squaredTimeWeightedDiscountedBurn initial q i

theorem squaredTimeWeightedDiscountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (i : Nat) :
    0 ≤ squaredTimeWeightedDiscountedBurn initial q i := by
  unfold squaredTimeWeightedDiscountedBurn
  exact mul_nonneg (sq_nonneg (i : Rat))
    (discountedBurn_nonneg hqNonneg hqLeOne hInitial i)

theorem cumulativeSquaredTimeWeightedDiscountedBurn_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    0 ≤ cumulativeSquaredTimeWeightedDiscountedBurn initial q n := by
  unfold cumulativeSquaredTimeWeightedDiscountedBurn
  exact Finset.sum_nonneg fun i _ =>
    squaredTimeWeightedDiscountedBurn_nonneg hqNonneg hqLeOne hInitial i

theorem cumulativeSquaredTimeWeightedDiscountedBurn_succ
    (initial q : Rat) (n : Nat) :
    cumulativeSquaredTimeWeightedDiscountedBurn initial q (n + 1) =
      cumulativeSquaredTimeWeightedDiscountedBurn initial q n +
        squaredTimeWeightedDiscountedBurn initial q n := by
  unfold cumulativeSquaredTimeWeightedDiscountedBurn
  simp [Finset.sum_range_succ]

theorem cumulativeSquaredTimeWeightedDiscountedBurn_le_horizon_sq_mul_cumulativeBurn
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeSquaredTimeWeightedDiscountedBurn initial q n ≤
      (n : Rat) ^ 2 * cumulativeDiscountedBurn initial q n := by
  unfold cumulativeSquaredTimeWeightedDiscountedBurn
  unfold squaredTimeWeightedDiscountedBurn cumulativeDiscountedBurn
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    have hIndex : (i : Rat) ≤ n := by
      exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hi)
    have hSq : (i : Rat) ^ 2 ≤ (n : Rat) ^ 2 := by
      nlinarith [sq_nonneg ((n : Rat) - (i : Rat))]
    exact mul_le_mul_of_nonneg_right hSq
      (discountedBurn_nonneg hqNonneg hqLeOne hInitial i)

theorem cumulativeSquaredTimeWeightedDiscountedBurn_le_horizon_sq_mul_initial
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial) (n : Nat) :
    cumulativeSquaredTimeWeightedDiscountedBurn initial q n ≤
      (n : Rat) ^ 2 * initial := by
  have hMoment :=
    cumulativeSquaredTimeWeightedDiscountedBurn_le_horizon_sq_mul_cumulativeBurn
      hqNonneg hqLeOne hInitial n
  have hBudget := cumulativeDiscountedBurn_le_initial hqNonneg hInitial n
  have hSqNonneg : 0 ≤ (n : Rat) ^ 2 := sq_nonneg (n : Rat)
  exact hMoment.trans (mul_le_mul_of_nonneg_left hBudget hSqNonneg)

theorem squaredTimeWeightedDiscountedBurn_tail (initial q : Rat) (m i : Nat) :
    squaredTimeWeightedDiscountedBurn initial q (m + i) =
      (m : Rat) ^ 2 * discountedBurn (initial * q ^ m) q i +
        2 * (m : Rat) * timeWeightedDiscountedBurn (initial * q ^ m) q i +
          squaredTimeWeightedDiscountedBurn (initial * q ^ m) q i := by
  unfold squaredTimeWeightedDiscountedBurn timeWeightedDiscountedBurn discountedBurn
  rw [pow_add]
  norm_num
  ring

theorem cumulativeSquaredTimeWeightedDiscountedBurn_split
    (initial q : Rat) (m n : Nat) :
    cumulativeSquaredTimeWeightedDiscountedBurn initial q (m + n) =
      cumulativeSquaredTimeWeightedDiscountedBurn initial q m +
        (m : Rat) ^ 2 * cumulativeDiscountedBurn (initial * q ^ m) q n +
          2 * (m : Rat) *
              cumulativeTimeWeightedDiscountedBurn (initial * q ^ m) q n +
            cumulativeSquaredTimeWeightedDiscountedBurn
              (initial * q ^ m) q n := by
  induction n with
  | zero =>
      simp [cumulativeDiscountedBurn, cumulativeTimeWeightedDiscountedBurn,
        cumulativeSquaredTimeWeightedDiscountedBurn]
  | succ n ih =>
      rw [Nat.add_succ]
      rw [cumulativeSquaredTimeWeightedDiscountedBurn_succ]
      rw [ih]
      rw [cumulativeDiscountedBurn_succ]
      rw [cumulativeTimeWeightedDiscountedBurn_succ]
      rw [cumulativeSquaredTimeWeightedDiscountedBurn_succ]
      rw [squaredTimeWeightedDiscountedBurn_tail]
      ring

theorem cumulativeSquaredTimeWeightedDiscountedBurn_tail_nonneg
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    0 ≤ cumulativeSquaredTimeWeightedDiscountedBurn (initial * q ^ m) q n := by
  have hTailInitial : 0 ≤ initial * q ^ m :=
    mul_nonneg hInitial (pow_nonneg hqNonneg m)
  exact cumulativeSquaredTimeWeightedDiscountedBurn_nonneg
    hqNonneg hqLeOne hTailInitial n

theorem cumulativeSquaredTimeWeightedDiscountedBurn_le_add_horizon
    {initial q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1) (hInitial : 0 ≤ initial)
    (m n : Nat) :
    cumulativeSquaredTimeWeightedDiscountedBurn initial q m ≤
      cumulativeSquaredTimeWeightedDiscountedBurn initial q (m + n) := by
  rw [cumulativeSquaredTimeWeightedDiscountedBurn_split]
  have hTailBurn :=
    cumulativeDiscountedBurn_tail_nonneg hqNonneg hqLeOne hInitial m n
  have hTailMoment :=
    cumulativeTimeWeightedDiscountedBurn_tail_nonneg hqNonneg hqLeOne hInitial m n
  have hTailSq :=
    cumulativeSquaredTimeWeightedDiscountedBurn_tail_nonneg
      hqNonneg hqLeOne hInitial m n
  have hMNonneg : 0 ≤ (m : Rat) := by exact_mod_cast Nat.zero_le m
  have hMSqNonneg : 0 ≤ (m : Rat) ^ 2 := sq_nonneg (m : Rat)
  have hTwoMNonneg : 0 ≤ 2 * (m : Rat) :=
    mul_nonneg (by norm_num) hMNonneg
  have hOffsetBurn :
      0 ≤ (m : Rat) ^ 2 * cumulativeDiscountedBurn (initial * q ^ m) q n :=
    mul_nonneg hMSqNonneg hTailBurn
  have hOffsetMoment :
      0 ≤
        2 * (m : Rat) *
          cumulativeTimeWeightedDiscountedBurn (initial * q ^ m) q n :=
    mul_nonneg hTwoMNonneg hTailMoment
  linarith

end MarketSystem

end DeFi

end LeanMathlib
