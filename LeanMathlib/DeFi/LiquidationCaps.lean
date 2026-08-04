import Mathlib
import LeanMathlib.DeFi.LendingHealth
import LeanMathlib.DeFi.RiskPolicy

namespace LeanMathlib

/--
Value-level liquidation transfer.

`debtRepaid` is how much debt the liquidator removes.
`collateralValueTaken` is the value extracted from the borrower at the current
price. Using value instead of collateral units keeps the proof surface linear.
-/
structure LiquidationTransfer where
  debtRepaid : Rat
  collateralValueTaken : Rat

/-- Zero-transfer step used by blocking policy actions. -/
def noLiquidation : LiquidationTransfer :=
  { debtRepaid := 0, collateralValueTaken := 0 }

/--
Net change in solvency margin caused by a liquidation transfer at a fixed
position threshold.
-/
def liquidationDelta (position : LendingPosition) (transfer : LiquidationTransfer) : Rat :=
  position.liquidationThreshold * transfer.debtRepaid - transfer.collateralValueTaken

/--
Post-liquidation solvency margin at a fixed price.

Positive `liquidationDelta` improves the position; negative `liquidationDelta`
means the liquidation worsens margin.
-/
def postLiquidationSolvencyMargin
    (position : LendingPosition) (price : Rat) (transfer : LiquidationTransfer) : Rat :=
  solvencyMargin position price + liquidationDelta position transfer

/--
Policy-level transfer choice.

- `allow` and `pauseBorrow` keep the uncapped liquidation path available.
- `capLiquidation` uses the capped transfer.
- `freezeMarket`, `quarantineOracle`, `governanceReview`, and `deny` block the
  liquidation path completely.
-/
def policyTransfer
    (action : LendingRiskAction)
    (capped uncapped : LiquidationTransfer) : LiquidationTransfer :=
  match action with
  | .allow => uncapped
  | .pauseBorrow => uncapped
  | .capLiquidation => capped
  | .freezeMarket => noLiquidation
  | .quarantineOracle => noLiquidation
  | .governanceReview => noLiquidation
  | .deny => noLiquidation

/-- Predicate for actions that block liquidation entirely. -/
def blocksLiquidation (action : LendingRiskAction) : Prop :=
  action = .freezeMarket ∨
    action = .quarantineOracle ∨
    action = .governanceReview ∨
    action = .deny

theorem postLiquidationSolvencyMargin_eq
    (position : LendingPosition)
    (price : Rat)
    (transfer : LiquidationTransfer) :
    postLiquidationSolvencyMargin position price transfer =
      collateralValue position price
        - position.liquidationThreshold * position.debt
        + position.liquidationThreshold * transfer.debtRepaid
        - transfer.collateralValueTaken := by
  dsimp [postLiquidationSolvencyMargin, solvencyMargin, liquidationDelta]
  ring

theorem liquidationDelta_eq_zero_of_noLiquidation
    (position : LendingPosition) :
    liquidationDelta position noLiquidation = 0 := by
  dsimp [liquidationDelta, noLiquidation]
  ring

theorem postLiquidationSolvencyMargin_eq_of_noLiquidation
    (position : LendingPosition)
    (price : Rat) :
    postLiquidationSolvencyMargin position price noLiquidation =
      solvencyMargin position price := by
  dsimp [postLiquidationSolvencyMargin]
  rw [liquidationDelta_eq_zero_of_noLiquidation, add_zero]

theorem liquidationDelta_nonneg_of_valueBound
    (position : LendingPosition)
    (transfer : LiquidationTransfer)
    (hBound :
      transfer.collateralValueTaken ≤
        position.liquidationThreshold * transfer.debtRepaid) :
    0 ≤ liquidationDelta position transfer := by
  dsimp [liquidationDelta]
  linarith

theorem postLiquidationSolvencyMargin_nonneg_of_solventAt_and_valueBound
    (position : LendingPosition)
    (price : Rat)
    (transfer : LiquidationTransfer)
    (hSolvent : solventAt position price)
    (hBound :
      transfer.collateralValueTaken ≤
        position.liquidationThreshold * transfer.debtRepaid) :
    0 ≤ postLiquidationSolvencyMargin position price transfer := by
  have hMargin : 0 ≤ solvencyMargin position price :=
    (solventAt_iff_nonneg_solvencyMargin position price).1 hSolvent
  have hDelta : 0 ≤ liquidationDelta position transfer :=
    liquidationDelta_nonneg_of_valueBound position transfer hBound
  dsimp [postLiquidationSolvencyMargin]
  exact add_nonneg hMargin hDelta

theorem postLiquidationSolvencyMargin_nonneg_of_adverseSolvent_inOracleEnvelope
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (transfer : LiquidationTransfer)
    (hCollateral : 0 ≤ position.collateral)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hSolventAdverse : solventAt position (adversePrice bounds))
    (hBound :
      transfer.collateralValueTaken ≤
        position.liquidationThreshold * transfer.debtRepaid) :
    0 ≤ postLiquidationSolvencyMargin position actualPrice transfer := by
  have hSolventActual : solventAt position actualPrice :=
    solventAt_of_inOracleEnvelope position bounds hCollateral hEnvelope hSolventAdverse
  exact postLiquidationSolvencyMargin_nonneg_of_solventAt_and_valueBound
    position actualPrice transfer hSolventActual hBound

theorem policyTransfer_eq_noLiquidation_of_blocksLiquidation
    {action : LendingRiskAction}
    (capped uncapped : LiquidationTransfer)
    (hBlock : blocksLiquidation action) :
    policyTransfer action capped uncapped = noLiquidation := by
  rcases hBlock with h | h | h | h <;> cases h <;> rfl

theorem postLiquidationSolvencyMargin_eq_pre_of_blocksLiquidation
    (position : LendingPosition)
    (price : Rat)
    {action : LendingRiskAction}
    (capped uncapped : LiquidationTransfer)
    (hBlock : blocksLiquidation action) :
    postLiquidationSolvencyMargin position price (policyTransfer action capped uncapped) =
      solvencyMargin position price := by
  rw [policyTransfer_eq_noLiquidation_of_blocksLiquidation capped uncapped hBlock]
  exact postLiquidationSolvencyMargin_eq_of_noLiquidation position price

theorem policyTransfer_pauseBorrow_eq_allow
    (capped uncapped : LiquidationTransfer) :
    policyTransfer .pauseBorrow capped uncapped =
      policyTransfer .allow capped uncapped := by
  rfl

theorem postLiquidationSolvencyMargin_cap_ge_allow_of_sameDebt_and_taken_le
    (position : LendingPosition)
    (price : Rat)
    (capped uncapped : LiquidationTransfer)
    (hDebt : capped.debtRepaid = uncapped.debtRepaid)
    (hTaken : capped.collateralValueTaken ≤ uncapped.collateralValueTaken) :
    postLiquidationSolvencyMargin position price (policyTransfer .allow capped uncapped) ≤
      postLiquidationSolvencyMargin
        position
        price
        (policyTransfer .capLiquidation capped uncapped) := by
  dsimp [policyTransfer, postLiquidationSolvencyMargin, liquidationDelta]
  rw [hDebt]
  linarith

theorem postLiquidationSolvencyMargin_pause_ge_allow_of_nonpos_uncappedDelta
    (position : LendingPosition)
    (price : Rat)
    (uncapped : LiquidationTransfer)
    (hDelta : liquidationDelta position uncapped ≤ 0) :
    postLiquidationSolvencyMargin position price uncapped ≤
      postLiquidationSolvencyMargin position price noLiquidation := by
  dsimp [postLiquidationSolvencyMargin]
  rw [liquidationDelta_eq_zero_of_noLiquidation]
  linarith

end LeanMathlib
