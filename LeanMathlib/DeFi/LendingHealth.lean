import Mathlib
import LeanMathlib.DeFi.OracleBounds

namespace LeanMathlib

/--
Required collateral value at the liquidation threshold. This is the minimum
value the position must maintain to remain solvent.
-/
def requiredCollateralValue (position : LendingPosition) : Rat :=
  position.liquidationThreshold * position.debt

/--
Normalized health factor.

This ratio is only economically meaningful when `requiredCollateralValue > 0`,
and theorems below state that assumption explicitly.
-/
def healthFactor (position : LendingPosition) (price : Rat) : Rat :=
  collateralValue position price / requiredCollateralValue position

/--
Maximum debt supported by the current collateral value and liquidation
threshold.

This is only meaningful when the liquidation threshold is positive.
-/
def maxSafeDebt (position : LendingPosition) (price : Rat) : Rat :=
  collateralValue position price / position.liquidationThreshold

theorem requiredCollateralValue_nonneg
    (position : LendingPosition)
    (hThreshold : 0 ≤ position.liquidationThreshold)
    (hDebt : 0 ≤ position.debt) :
    0 ≤ requiredCollateralValue position := by
  dsimp [requiredCollateralValue]
  exact mul_nonneg hThreshold hDebt

theorem requiredCollateralValue_pos
    (position : LendingPosition)
    (hThreshold : 0 < position.liquidationThreshold)
    (hDebt : 0 < position.debt) :
    0 < requiredCollateralValue position := by
  dsimp [requiredCollateralValue]
  exact mul_pos hThreshold hDebt

theorem healthFactor_nonneg
    (position : LendingPosition)
    {price : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hPrice : 0 ≤ price)
    (hRequired : 0 < requiredCollateralValue position) :
    0 ≤ healthFactor position price := by
  dsimp [healthFactor]
  exact div_nonneg (collateralValue_nonneg position hCollateral hPrice) hRequired.le

theorem healthFactor_mono
    (position : LendingPosition)
    {price₁ price₂ : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hRequired : 0 < requiredCollateralValue position)
    (hPrice : price₁ ≤ price₂) :
    healthFactor position price₁ ≤ healthFactor position price₂ := by
  dsimp [healthFactor]
  exact div_le_div_of_nonneg_right
    (collateralValue_mono position hCollateral hPrice)
    hRequired.le

theorem solventAt_iff_one_le_healthFactor
    (position : LendingPosition)
    (price : Rat)
    (hRequired : 0 < requiredCollateralValue position) :
    solventAt position price ↔ 1 ≤ healthFactor position price := by
  calc
    solventAt position price
      ↔ requiredCollateralValue position ≤ collateralValue position price := by
          rfl
    _ ↔ (1 : Rat) * requiredCollateralValue position ≤ collateralValue position price := by
          simp
    _ ↔ (1 : Rat) ≤ collateralValue position price / requiredCollateralValue position := by
          exact (le_div_iff₀ hRequired).symm
    _ ↔ (1 : Rat) ≤ healthFactor position price := by
          rfl

theorem healthFactor_at_adverse_le_healthFactor_of_inOracleEnvelope
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hRequired : 0 < requiredCollateralValue position)
    (hEnvelope : inOracleEnvelope bounds actualPrice) :
    healthFactor position (adversePrice bounds) ≤ healthFactor position actualPrice := by
  exact healthFactor_mono position hCollateral hRequired hEnvelope.1

theorem solventAt_of_worstCaseHealthFactor_ge_one
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hRequired : 0 < requiredCollateralValue position)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hHealth : 1 ≤ healthFactor position (adversePrice bounds)) :
    solventAt position actualPrice := by
  have hAdverse :
      solventAt position (adversePrice bounds) := by
    exact (solventAt_iff_one_le_healthFactor position (adversePrice bounds) hRequired).2 hHealth
  exact solventAt_of_inOracleEnvelope position bounds hCollateral hEnvelope hAdverse

theorem maxSafeDebt_mono
    (position : LendingPosition)
    {price₁ price₂ : Rat}
    (hThreshold : 0 < position.liquidationThreshold)
    (hCollateral : 0 ≤ position.collateral)
    (hPrice : price₁ ≤ price₂) :
    maxSafeDebt position price₁ ≤ maxSafeDebt position price₂ := by
  dsimp [maxSafeDebt]
  exact div_le_div_of_nonneg_right
    (collateralValue_mono position hCollateral hPrice)
    hThreshold.le

theorem debt_le_maxSafeDebt_iff
    (position : LendingPosition)
    (price : Rat)
    (hThreshold : 0 < position.liquidationThreshold) :
    position.debt ≤ maxSafeDebt position price ↔ solventAt position price := by
  calc
    position.debt ≤ maxSafeDebt position price
      ↔ position.debt * position.liquidationThreshold ≤ collateralValue position price := by
          simpa [maxSafeDebt, collateralValue] using
            (le_div_iff₀ hThreshold :
              position.debt ≤ collateralValue position price / position.liquidationThreshold ↔
                position.debt * position.liquidationThreshold ≤ collateralValue position price)
    _ ↔ solventAt position price := by
          simp [solventAt, collateralValue, mul_comm]

theorem debt_le_maxSafeDebt_of_inOracleEnvelope
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (hThreshold : 0 < position.liquidationThreshold)
    (hCollateral : 0 ≤ position.collateral)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hDebt : position.debt ≤ maxSafeDebt position (adversePrice bounds)) :
    position.debt ≤ maxSafeDebt position actualPrice := by
  exact le_trans hDebt (maxSafeDebt_mono position hThreshold hCollateral hEnvelope.1)

theorem solventAt_of_debt_le_maxSafeDebt_inOracleEnvelope
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (hThreshold : 0 < position.liquidationThreshold)
    (hCollateral : 0 ≤ position.collateral)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hDebt : position.debt ≤ maxSafeDebt position (adversePrice bounds)) :
    solventAt position actualPrice := by
  have hAdverse : solventAt position (adversePrice bounds) := by
    exact (debt_le_maxSafeDebt_iff position (adversePrice bounds) hThreshold).1 hDebt
  exact solventAt_of_inOracleEnvelope position bounds hCollateral hEnvelope hAdverse

end LeanMathlib
