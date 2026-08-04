import LeanMathlib.DeFi.TokenomicsSupply

open Finset

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Cadence-gated reward stream. `cadence = 1` is daily in a daily clock, `cadence = 7`
is weekly in a daily clock, and `cadence = 0` disables releases. -/
def periodicDrip (amount : Rat) (cadence t : Nat) : Rat :=
  if cadence = 0 then 0 else if cadence ∣ t + 1 then amount else 0

/-- Cumulative released amount from an arbitrary drip stream over the first `n` ticks. -/
def cumulativeDrip (drip : Nat → Rat) (n : Nat) : Rat :=
  ∑ t ∈ Finset.range n, drip t

/-- Cumulative released amount from a fixed-amount periodic drip. -/
def cumulativePeriodicDrip (amount : Rat) (cadence n : Nat) : Rat :=
  cumulativeDrip (periodicDrip amount cadence) n

/-- Daily release when the protocol clock is measured in days. -/
def dailyDrip (amount : Rat) : Nat → Rat :=
  periodicDrip amount 1

/-- Weekly release when the protocol clock is measured in days. -/
def weeklyDrip (amount : Rat) : Nat → Rat :=
  periodicDrip amount 7

/-- Total staking or participation weight used for pro-rata drip accounting. -/
def totalDripWeight {ι : Type*} [Fintype ι] (weight : ι → Rat) : Rat :=
  ∑ i, weight i

/-- A user's cumulative pro-rata claim from a drip stream. -/
def userDripClaim {ι : Type*} [Fintype ι]
    (drip : Nat → Rat) (weight : ι → Rat) (i : ι) (n : Nat) : Rat :=
  cumulativeDrip drip n * weight i / totalDripWeight weight

/-- Total cumulative claims across all users. -/
def totalDripClaims {ι : Type*} [Fintype ι]
    (drip : Nat → Rat) (weight : ι → Rat) (n : Nat) : Rat :=
  ∑ i, userDripClaim drip weight i n

theorem periodicDrip_nonneg
    {amount : Rat} (hAmount : 0 ≤ amount) (cadence t : Nat) :
    0 ≤ periodicDrip amount cadence t := by
  unfold periodicDrip
  split
  · norm_num
  · split
    · exact hAmount
    · norm_num

theorem periodicDrip_le_amount
    {amount : Rat} (hAmount : 0 ≤ amount) (cadence t : Nat) :
    periodicDrip amount cadence t ≤ amount := by
  unfold periodicDrip
  split
  · exact hAmount
  · split
    · exact le_rfl
    · exact hAmount

theorem cumulativeDrip_nonneg
    {drip : Nat → Rat} (hDrip : ∀ t, 0 ≤ drip t) (n : Nat) :
    0 ≤ cumulativeDrip drip n := by
  unfold cumulativeDrip
  exact sum_nonneg fun t _ht => hDrip t

theorem cumulativePeriodicDrip_nonneg
    {amount : Rat} (hAmount : 0 ≤ amount) (cadence n : Nat) :
    0 ≤ cumulativePeriodicDrip amount cadence n := by
  unfold cumulativePeriodicDrip
  exact cumulativeDrip_nonneg (periodicDrip_nonneg hAmount cadence) n

theorem cumulativePeriodicDrip_le_horizon_mul_amount
    {amount : Rat} (hAmount : 0 ≤ amount) (cadence n : Nat) :
    cumulativePeriodicDrip amount cadence n ≤ (n : Rat) * amount := by
  unfold cumulativePeriodicDrip cumulativeDrip
  calc
    (∑ t ∈ Finset.range n, periodicDrip amount cadence t)
        ≤ ∑ t ∈ Finset.range n, amount := by
          exact sum_le_sum fun t _ht => periodicDrip_le_amount hAmount cadence t
    _ = (n : Rat) * amount := by
          simp

theorem dailyDrip_eq_amount (amount : Rat) (t : Nat) :
    dailyDrip amount t = amount := by
  unfold dailyDrip periodicDrip
  simp

theorem weeklyDrip_eq_amount_of_dvd
    (amount : Rat) {t : Nat} (hRelease : 7 ∣ t + 1) :
    weeklyDrip amount t = amount := by
  unfold weeklyDrip periodicDrip
  simp [hRelease]

theorem weeklyDrip_eq_zero_of_not_dvd
    (amount : Rat) {t : Nat} (hNoRelease : ¬ 7 ∣ t + 1) :
    weeklyDrip amount t = 0 := by
  unfold weeklyDrip periodicDrip
  simp [hNoRelease]

theorem cumulativeDailyDrip_eq_horizon_mul_amount
    (amount : Rat) (n : Nat) :
    cumulativeDrip (dailyDrip amount) n = (n : Rat) * amount := by
  unfold cumulativeDrip
  calc
    (∑ t ∈ Finset.range n, dailyDrip amount t)
        = ∑ _t ∈ Finset.range n, amount := by
          exact sum_congr rfl fun t _ht => dailyDrip_eq_amount amount t
    _ = (n : Rat) * amount := by
          simp

theorem cumulativeWeeklyDrip_nonneg
    {amount : Rat} (hAmount : 0 ≤ amount) (n : Nat) :
    0 ≤ cumulativeDrip (weeklyDrip amount) n := by
  unfold weeklyDrip
  exact cumulativePeriodicDrip_nonneg hAmount 7 n

theorem cumulativeWeeklyDrip_le_horizon_mul_amount
    {amount : Rat} (hAmount : 0 ≤ amount) (n : Nat) :
    cumulativeDrip (weeklyDrip amount) n ≤ (n : Rat) * amount := by
  unfold weeklyDrip
  exact cumulativePeriodicDrip_le_horizon_mul_amount hAmount 7 n

theorem cumulativeDrip_succ
    (drip : Nat → Rat) (n : Nat) :
    cumulativeDrip drip (n + 1) = cumulativeDrip drip n + drip n := by
  unfold cumulativeDrip
  simp [Finset.sum_range_succ]

theorem totalDripClaims_eq_cumulativeDrip
    {ι : Type*} [Fintype ι]
    (drip : Nat → Rat) (weight : ι → Rat) (n : Nat)
    (hTotal : totalDripWeight weight ≠ 0) :
    totalDripClaims drip weight n = cumulativeDrip drip n := by
  have hTotal' : (∑ j, weight j) ≠ 0 := by
    simpa [totalDripWeight] using hTotal
  unfold totalDripClaims userDripClaim totalDripWeight
  calc
    (∑ i, cumulativeDrip drip n * weight i / ∑ j, weight j)
        = (cumulativeDrip drip n * ∑ i, weight i) / ∑ j, weight j := by
          rw [← Finset.sum_div]
          congr 1
          rw [Finset.mul_sum]
    _ = cumulativeDrip drip n := by
          field_simp [hTotal']

theorem userDripClaim_nonneg
    {ι : Type*} [Fintype ι]
    {drip : Nat → Rat} {weight : ι → Rat} {i : ι} {n : Nat}
    (hDrip : ∀ t, 0 ≤ drip t)
    (hWeight : 0 ≤ weight i)
    (hTotal : 0 < totalDripWeight weight) :
    0 ≤ userDripClaim drip weight i n := by
  unfold userDripClaim
  have hCum : 0 ≤ cumulativeDrip drip n := cumulativeDrip_nonneg hDrip n
  exact div_nonneg (mul_nonneg hCum hWeight) (le_of_lt hTotal)

theorem totalDripClaims_nonneg
    {ι : Type*} [Fintype ι]
    {drip : Nat → Rat} {weight : ι → Rat} {n : Nat}
    (hDrip : ∀ t, 0 ≤ drip t)
    (hWeight : ∀ i, 0 ≤ weight i)
    (hTotal : 0 < totalDripWeight weight) :
    0 ≤ totalDripClaims drip weight n := by
  unfold totalDripClaims
  exact sum_nonneg fun i _hi =>
    userDripClaim_nonneg hDrip (hWeight i) hTotal

theorem userDripClaim_le_cumulativeDrip
    {ι : Type*} [Fintype ι]
    {drip : Nat → Rat} {weight : ι → Rat} {i : ι} {n : Nat}
    (hDrip : ∀ t, 0 ≤ drip t)
    (hWeightNonneg : ∀ j, 0 ≤ weight j)
    (hTotal : 0 < totalDripWeight weight) :
    userDripClaim drip weight i n ≤ cumulativeDrip drip n := by
  unfold userDripClaim
  have hCum : 0 ≤ cumulativeDrip drip n := cumulativeDrip_nonneg hDrip n
  have hWeightLeTotal : weight i ≤ totalDripWeight weight := by
    unfold totalDripWeight
    exact single_le_sum (fun j _hj => hWeightNonneg j) (mem_univ i)
  have hRatioLe : weight i / totalDripWeight weight ≤ 1 := by
    exact (div_le_one hTotal).mpr hWeightLeTotal
  have hClaimEq :
      cumulativeDrip drip n * weight i / totalDripWeight weight =
        cumulativeDrip drip n * (weight i / totalDripWeight weight) := by
    ring
  rw [hClaimEq]
  calc
    cumulativeDrip drip n * (weight i / totalDripWeight weight)
        ≤ cumulativeDrip drip n * 1 :=
          mul_le_mul_of_nonneg_left hRatioLe hCum
    _ = cumulativeDrip drip n := by ring

end MarketSystem

end DeFi

end LeanMathlib
