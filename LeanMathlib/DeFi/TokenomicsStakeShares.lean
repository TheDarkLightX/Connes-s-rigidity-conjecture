import LeanMathlib.DeFi.TokenomicsDripAccounting

open Finset

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

/-- Principal after applying a duration bonus. This deliberately excludes any size bonus,
so equal-duration share minting is linear in principal. -/
def durationAdjustedPrincipal
    (principal : Rat) (bonus : Nat → Rat) (duration : Nat) : Rat :=
  principal * bonus duration

/-- Stake shares minted from principal, duration bonus, and the current global share rate. -/
def stakeShares
    (principal : Rat) (bonus : Nat → Rat) (duration : Nat) (shareRate : Rat) : Rat :=
  durationAdjustedPrincipal principal bonus duration / shareRate

/-- Total shares across a finite stake set. -/
def totalStakeShares {ι : Type*} [Fintype ι]
    (principal : ι → Rat) (bonus : Nat → Rat) (duration : ι → Nat)
    (shareRate : Rat) : Rat :=
  ∑ i, stakeShares (principal i) bonus (duration i) shareRate

/-- Payout against a fixed reward pool and fixed total share denominator. -/
def stakePayout (rewardPool stake totalShares : Rat) : Rat :=
  rewardPool * stake / totalShares

/-- Total payouts across a finite share vector. -/
def totalStakePayouts {ι : Type*} [Fintype ι]
    (rewardPool : Rat) (stake : ι → Rat) : Rat :=
  ∑ i, stakePayout rewardPool (stake i) (∑ j, stake j)

theorem durationAdjustedPrincipal_add
    (a b : Rat) (bonus : Nat → Rat) (duration : Nat) :
    durationAdjustedPrincipal (a + b) bonus duration =
      durationAdjustedPrincipal a bonus duration +
        durationAdjustedPrincipal b bonus duration := by
  unfold durationAdjustedPrincipal
  ring

theorem durationAdjustedPrincipal_zero
    (bonus : Nat → Rat) (duration : Nat) :
    durationAdjustedPrincipal 0 bonus duration = 0 := by
  unfold durationAdjustedPrincipal
  ring

theorem durationAdjustedPrincipal_nonneg
    {principal : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonus : 0 ≤ bonus duration) :
    0 ≤ durationAdjustedPrincipal principal bonus duration := by
  unfold durationAdjustedPrincipal
  exact mul_nonneg hPrincipal hBonus

theorem durationAdjustedPrincipal_mono_duration
    {principal : Rat} {bonus : Nat → Rat} {short long : Nat}
    (hPrincipal : 0 ≤ principal) (hBonus : bonus short ≤ bonus long) :
    durationAdjustedPrincipal principal bonus short ≤
      durationAdjustedPrincipal principal bonus long := by
  unfold durationAdjustedPrincipal
  exact mul_le_mul_of_nonneg_left hBonus hPrincipal

theorem durationAdjustedPrincipal_mono_principal
    {a b : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : a ≤ b) (hBonus : 0 ≤ bonus duration) :
    durationAdjustedPrincipal a bonus duration ≤
      durationAdjustedPrincipal b bonus duration := by
  unfold durationAdjustedPrincipal
  exact mul_le_mul_of_nonneg_right hPrincipal hBonus

theorem durationAdjustedPrincipal_scale
    (k principal : Rat) (bonus : Nat → Rat) (duration : Nat) :
    durationAdjustedPrincipal (k * principal) bonus duration =
      k * durationAdjustedPrincipal principal bonus duration := by
  unfold durationAdjustedPrincipal
  ring

theorem durationAdjustedPrincipal_le_cap
    {principal cap : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonusCap : bonus duration ≤ cap) :
    durationAdjustedPrincipal principal bonus duration ≤ principal * cap := by
  unfold durationAdjustedPrincipal
  exact mul_le_mul_of_nonneg_left hBonusCap hPrincipal

theorem stakeShares_add_principal
    (a b : Rat) (bonus : Nat → Rat) (duration : Nat) (shareRate : Rat) :
    stakeShares (a + b) bonus duration shareRate =
      stakeShares a bonus duration shareRate +
        stakeShares b bonus duration shareRate := by
  unfold stakeShares durationAdjustedPrincipal
  ring

theorem stakeShares_zero_principal
    (bonus : Nat → Rat) (duration : Nat) (shareRate : Rat) :
    stakeShares 0 bonus duration shareRate = 0 := by
  unfold stakeShares durationAdjustedPrincipal
  ring

theorem stakeShares_scale_principal
    (k principal : Rat) (bonus : Nat → Rat) (duration : Nat) (shareRate : Rat) :
    stakeShares (k * principal) bonus duration shareRate =
      k * stakeShares principal bonus duration shareRate := by
  unfold stakeShares durationAdjustedPrincipal
  ring

/-- Splitting one equal-duration stake into two stakes gives exactly the same shares. -/
theorem stakeShares_split_neutral
    (a b : Rat) (bonus : Nat → Rat) (duration : Nat) (shareRate : Rat) :
    stakeShares (a + b) bonus duration shareRate =
      stakeShares a bonus duration shareRate +
        stakeShares b bonus duration shareRate :=
  stakeShares_add_principal a b bonus duration shareRate

/-- Merging two equal-duration stakes gives exactly the same shares. -/
theorem stakeShares_merge_neutral
    (a b : Rat) (bonus : Nat → Rat) (duration : Nat) (shareRate : Rat) :
    stakeShares a bonus duration shareRate +
        stakeShares b bonus duration shareRate =
      stakeShares (a + b) bonus duration shareRate := by
  rw [stakeShares_add_principal]

theorem stakeShares_nonneg
    {principal shareRate : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonus : 0 ≤ bonus duration)
    (hShareRate : 0 < shareRate) :
    0 ≤ stakeShares principal bonus duration shareRate := by
  unfold stakeShares
  exact div_nonneg
    (durationAdjustedPrincipal_nonneg hPrincipal hBonus)
    (le_of_lt hShareRate)

theorem stakeShares_mono_principal
    {a b shareRate : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : a ≤ b) (hBonus : 0 ≤ bonus duration)
    (hShareRate : 0 < shareRate) :
    stakeShares a bonus duration shareRate ≤
      stakeShares b bonus duration shareRate := by
  unfold stakeShares
  exact div_le_div_of_nonneg_right
    (durationAdjustedPrincipal_mono_principal hPrincipal hBonus)
    (le_of_lt hShareRate)

/-- Longer duration gives weakly more shares when the duration bonus is monotone. -/
theorem stakeShares_mono_duration
    {principal shareRate : Rat} {bonus : Nat → Rat} {short long : Nat}
    (hPrincipal : 0 ≤ principal) (hBonus : bonus short ≤ bonus long)
    (hShareRate : 0 < shareRate) :
    stakeShares principal bonus short shareRate ≤
      stakeShares principal bonus long shareRate := by
  unfold stakeShares
  exact div_le_div_of_nonneg_right
    (durationAdjustedPrincipal_mono_duration hPrincipal hBonus)
    (le_of_lt hShareRate)

/-- A capped duration multiplier gives a protocol-level upper bound on share advantage. -/
theorem stakeShares_le_capped_duration_advantage
    {principal shareRate cap : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonusCap : bonus duration ≤ cap)
    (hShareRate : 0 < shareRate) :
    stakeShares principal bonus duration shareRate ≤ principal * cap / shareRate := by
  unfold stakeShares
  exact div_le_div_of_nonneg_right
    (durationAdjustedPrincipal_le_cap hPrincipal hBonusCap)
    (le_of_lt hShareRate)

theorem stakeShares_between_zero_and_capped_advantage
    {principal shareRate cap : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonusNonneg : 0 ≤ bonus duration)
    (hBonusCap : bonus duration ≤ cap) (hShareRate : 0 < shareRate) :
    0 ≤ stakeShares principal bonus duration shareRate ∧
      stakeShares principal bonus duration shareRate ≤ principal * cap / shareRate :=
  ⟨stakeShares_nonneg hPrincipal hBonusNonneg hShareRate,
    stakeShares_le_capped_duration_advantage hPrincipal hBonusCap hShareRate⟩

/-- A higher share rate weakly reduces shares minted for the same economic commitment. -/
theorem stakeShares_anti_mono_shareRate
    {principal oldRate newRate : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonus : 0 ≤ bonus duration)
    (hOldRate : 0 < oldRate) (hRate : oldRate ≤ newRate) :
    stakeShares principal bonus duration newRate ≤
      stakeShares principal bonus duration oldRate := by
  unfold stakeShares
  have hAdjusted : 0 ≤ durationAdjustedPrincipal principal bonus duration :=
    durationAdjustedPrincipal_nonneg hPrincipal hBonus
  exact div_le_div_of_nonneg_left hAdjusted hOldRate hRate

/-- Share-rate ratchets are anti-dilutive: later entrants at a weakly higher rate
cannot mint more shares for the same principal and duration. -/
theorem stakeShares_ratchet_anti_dilution
    {principal currentRate nextRate : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonus : 0 ≤ bonus duration)
    (hCurrentRate : 0 < currentRate) (hRatchet : currentRate ≤ nextRate) :
    stakeShares principal bonus duration nextRate ≤
      stakeShares principal bonus duration currentRate :=
  stakeShares_anti_mono_shareRate
    hPrincipal hBonus hCurrentRate hRatchet

theorem stakeShares_ratchet_le_capped_current_rate
    {principal currentRate nextRate cap : Rat} {bonus : Nat → Rat} {duration : Nat}
    (hPrincipal : 0 ≤ principal) (hBonusNonneg : 0 ≤ bonus duration)
    (hBonusCap : bonus duration ≤ cap)
    (hCurrentRate : 0 < currentRate) (hRatchet : currentRate ≤ nextRate) :
    stakeShares principal bonus duration nextRate ≤ principal * cap / currentRate := by
  have hRatchetLe :
      stakeShares principal bonus duration nextRate ≤
        stakeShares principal bonus duration currentRate :=
    stakeShares_ratchet_anti_dilution
      hPrincipal hBonusNonneg hCurrentRate hRatchet
  have hCap :
      stakeShares principal bonus duration currentRate ≤
        principal * cap / currentRate :=
    stakeShares_le_capped_duration_advantage
      hPrincipal hBonusCap hCurrentRate
  exact hRatchetLe.trans hCap

/-- Passive long-hold advantage: at the same principal, a longer lock at the current
share rate weakly dominates a shorter lock minted after a nondecreasing share-rate ratchet. -/
theorem stakeShares_longer_currentRate_ge_shorter_nextRate
    {principal currentRate nextRate : Rat} {bonus : Nat → Rat} {short long : Nat}
    (hPrincipal : 0 ≤ principal) (hBonusShortNonneg : 0 ≤ bonus short)
    (hBonusMono : bonus short ≤ bonus long)
    (hCurrentRate : 0 < currentRate) (hRatchet : currentRate ≤ nextRate) :
    stakeShares principal bonus short nextRate ≤
      stakeShares principal bonus long currentRate := by
  have hRatchetLe :
      stakeShares principal bonus short nextRate ≤
        stakeShares principal bonus short currentRate :=
    stakeShares_ratchet_anti_dilution
      hPrincipal hBonusShortNonneg hCurrentRate hRatchet
  have hDurationLe :
      stakeShares principal bonus short currentRate ≤
        stakeShares principal bonus long currentRate :=
    stakeShares_mono_duration hPrincipal hBonusMono hCurrentRate
  exact hRatchetLe.trans hDurationLe

theorem totalStakeShares_nonneg
    {ι : Type*} [Fintype ι]
    {principal : ι → Rat} {bonus : Nat → Rat} {duration : ι → Nat}
    {shareRate : Rat}
    (hPrincipal : ∀ i, 0 ≤ principal i)
    (hBonus : ∀ i, 0 ≤ bonus (duration i))
    (hShareRate : 0 < shareRate) :
    0 ≤ totalStakeShares principal bonus duration shareRate := by
  unfold totalStakeShares
  exact sum_nonneg fun i _hi =>
    stakeShares_nonneg (hPrincipal i) (hBonus i) hShareRate

theorem stakePayout_add_stake
    (rewardPool x y totalShares : Rat) :
    stakePayout rewardPool (x + y) totalShares =
      stakePayout rewardPool x totalShares +
        stakePayout rewardPool y totalShares := by
  unfold stakePayout
  ring

theorem stakePayout_split_neutral
    (rewardPool a b totalShares shareRate : Rat)
    (bonus : Nat → Rat) (duration : Nat) :
    stakePayout rewardPool
        (stakeShares (a + b) bonus duration shareRate) totalShares =
      stakePayout rewardPool
          (stakeShares a bonus duration shareRate) totalShares +
        stakePayout rewardPool
          (stakeShares b bonus duration shareRate) totalShares := by
  rw [stakeShares_add_principal, stakePayout_add_stake]

theorem totalStakePayouts_eq_rewardPool
    {ι : Type*} [Fintype ι]
    (rewardPool : Rat) (stake : ι → Rat)
    (hTotal : (∑ j, stake j) ≠ 0) :
    totalStakePayouts rewardPool stake = rewardPool := by
  unfold totalStakePayouts stakePayout
  calc
    (∑ i, rewardPool * stake i / ∑ j, stake j)
        = (rewardPool * ∑ i, stake i) / ∑ j, stake j := by
          rw [← Finset.sum_div]
          congr 1
          rw [Finset.mul_sum]
    _ = rewardPool := by
          field_simp [hTotal]

theorem stakePayout_nonneg
    {rewardPool stake totalShares : Rat}
    (hRewardPool : 0 ≤ rewardPool) (hStake : 0 ≤ stake)
    (hTotalShares : 0 < totalShares) :
    0 ≤ stakePayout rewardPool stake totalShares := by
  unfold stakePayout
  exact div_nonneg (mul_nonneg hRewardPool hStake) (le_of_lt hTotalShares)

theorem stakePayout_le_rewardPool
    {rewardPool stake totalShares : Rat}
    (hRewardPool : 0 ≤ rewardPool)
    (hStakeLeTotal : stake ≤ totalShares) (hTotalShares : 0 < totalShares) :
    stakePayout rewardPool stake totalShares ≤ rewardPool := by
  unfold stakePayout
  have hRatioLe : stake / totalShares ≤ 1 := by
    exact (div_le_one hTotalShares).mpr hStakeLeTotal
  have hEq : rewardPool * stake / totalShares =
      rewardPool * (stake / totalShares) := by
    ring
  rw [hEq]
  calc
    rewardPool * (stake / totalShares) ≤ rewardPool * 1 :=
      mul_le_mul_of_nonneg_left hRatioLe hRewardPool
    _ = rewardPool := by ring

theorem stakePayout_between_zero_and_rewardPool
    {rewardPool stake totalShares : Rat}
    (hRewardPool : 0 ≤ rewardPool) (hStakeNonneg : 0 ≤ stake)
    (hStakeLeTotal : stake ≤ totalShares) (hTotalShares : 0 < totalShares) :
    0 ≤ stakePayout rewardPool stake totalShares ∧
      stakePayout rewardPool stake totalShares ≤ rewardPool :=
  ⟨stakePayout_nonneg hRewardPool hStakeNonneg hTotalShares,
    stakePayout_le_rewardPool hRewardPool hStakeLeTotal hTotalShares⟩

end MarketSystem

end DeFi

end LeanMathlib
