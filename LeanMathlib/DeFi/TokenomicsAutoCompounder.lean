import LeanMathlib.DeFi.TokenomicsDripAccounting

open Finset

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Balance after automatically reinvesting all released drip rewards into principal. -/
def reinvestedDripBalance (initial : Rat) (drip : Nat → Rat) (n : Nat) : Rat :=
  initial + cumulativeDrip drip n

/-- Balance under an arbitrary per-period multiplicative compounding factor. -/
def factorCompoundBalance (initial : Rat) (factor : Nat → Rat) (n : Nat) : Rat :=
  initial * ∏ t ∈ Finset.range n, factor t

/-- Balance under a constant per-period rate, with factor `1 + rate`. -/
def constantRateCompoundBalance (initial rate : Rat) (n : Nat) : Rat :=
  factorCompoundBalance initial (fun _t => 1 + rate) n

theorem reinvestedDripBalance_sub_initial
    (initial : Rat) (drip : Nat → Rat) (n : Nat) :
    reinvestedDripBalance initial drip n - initial = cumulativeDrip drip n := by
  unfold reinvestedDripBalance
  ring

theorem reinvestedDripBalance_succ
    (initial : Rat) (drip : Nat → Rat) (n : Nat) :
    reinvestedDripBalance initial drip (n + 1) =
      reinvestedDripBalance initial drip n + drip n := by
  unfold reinvestedDripBalance
  rw [cumulativeDrip_succ]
  ring

theorem reinvestedDripBalance_nonneg
    {initial : Rat} {drip : Nat → Rat}
    (hInitial : 0 ≤ initial) (hDrip : ∀ t, 0 ≤ drip t) (n : Nat) :
    0 ≤ reinvestedDripBalance initial drip n := by
  unfold reinvestedDripBalance
  exact add_nonneg hInitial (cumulativeDrip_nonneg hDrip n)

theorem reinvestedDripBalance_mono_succ
    {initial : Rat} {drip : Nat → Rat}
    (hDrip : ∀ t, 0 ≤ drip t) (n : Nat) :
    reinvestedDripBalance initial drip n ≤
      reinvestedDripBalance initial drip (n + 1) := by
  rw [reinvestedDripBalance_succ]
  exact le_add_of_nonneg_right (hDrip n)

theorem reinvestedDailyBalance_eq_initial_add_horizon_mul_amount
    (initial amount : Rat) (n : Nat) :
    reinvestedDripBalance initial (dailyDrip amount) n =
      initial + (n : Rat) * amount := by
  unfold reinvestedDripBalance
  rw [cumulativeDailyDrip_eq_horizon_mul_amount]

theorem factorCompoundBalance_zero
    (initial : Rat) (factor : Nat → Rat) :
    factorCompoundBalance initial factor 0 = initial := by
  unfold factorCompoundBalance
  simp

theorem factorCompoundBalance_succ
    (initial : Rat) (factor : Nat → Rat) (n : Nat) :
    factorCompoundBalance initial factor (n + 1) =
      factorCompoundBalance initial factor n * factor n := by
  unfold factorCompoundBalance
  rw [Finset.prod_range_succ]
  ring

theorem factorCompoundBalance_nonneg
    {initial : Rat} {factor : Nat → Rat}
    (hInitial : 0 ≤ initial) (hFactor : ∀ t, 0 ≤ factor t) (n : Nat) :
    0 ≤ factorCompoundBalance initial factor n := by
  unfold factorCompoundBalance
  exact mul_nonneg hInitial (prod_nonneg fun t _ht => hFactor t)

theorem factorCompoundBalance_mono_succ
    {initial : Rat} {factor : Nat → Rat}
    (hInitial : 0 ≤ initial) (hFactorNonneg : ∀ t, 0 ≤ factor t)
    (hFactorGrowth : ∀ t, 1 ≤ factor t) (n : Nat) :
    factorCompoundBalance initial factor n ≤
      factorCompoundBalance initial factor (n + 1) := by
  rw [factorCompoundBalance_succ]
  have hBalance : 0 ≤ factorCompoundBalance initial factor n :=
    factorCompoundBalance_nonneg hInitial hFactorNonneg n
  calc
    factorCompoundBalance initial factor n
        = factorCompoundBalance initial factor n * 1 := by ring
    _ ≤ factorCompoundBalance initial factor n * factor n :=
        mul_le_mul_of_nonneg_left (hFactorGrowth n) hBalance

theorem constantRateCompoundBalance_eq_pow
    (initial rate : Rat) (n : Nat) :
    constantRateCompoundBalance initial rate n = initial * (1 + rate) ^ n := by
  unfold constantRateCompoundBalance factorCompoundBalance
  simp

theorem constantRateCompoundBalance_succ
    (initial rate : Rat) (n : Nat) :
    constantRateCompoundBalance initial rate (n + 1) =
      constantRateCompoundBalance initial rate n * (1 + rate) := by
  unfold constantRateCompoundBalance
  exact factorCompoundBalance_succ initial (fun _t => 1 + rate) n

theorem constantRateCompoundBalance_nonneg
    {initial rate : Rat}
    (hInitial : 0 ≤ initial) (hFactor : 0 ≤ 1 + rate) (n : Nat) :
    0 ≤ constantRateCompoundBalance initial rate n := by
  unfold constantRateCompoundBalance
  exact factorCompoundBalance_nonneg hInitial (fun _t => hFactor) n

theorem constantRateCompoundBalance_mono_succ
    {initial rate : Rat}
    (hInitial : 0 ≤ initial) (hFactor : 1 ≤ 1 + rate) (n : Nat) :
    constantRateCompoundBalance initial rate n ≤
      constantRateCompoundBalance initial rate (n + 1) := by
  unfold constantRateCompoundBalance
  exact factorCompoundBalance_mono_succ hInitial
    (fun t => le_trans (by norm_num : (0 : Rat) ≤ 1) (hFactor : 1 ≤ 1 + rate))
    (fun _t => hFactor) n

theorem constantRateCompoundBalance_split
    (initial rate : Rat) (m n : Nat) :
    constantRateCompoundBalance initial rate (m + n) =
      constantRateCompoundBalance (constantRateCompoundBalance initial rate m) rate n := by
  rw [constantRateCompoundBalance_eq_pow]
  rw [constantRateCompoundBalance_eq_pow]
  rw [constantRateCompoundBalance_eq_pow]
  rw [pow_add]
  ring

end MarketSystem

end DeFi

end LeanMathlib
