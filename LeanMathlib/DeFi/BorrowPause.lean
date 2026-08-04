import Mathlib
import LeanMathlib.DeFi.LendingHealth

namespace LeanMathlib

/--
Minimal borrowing controller state.

This is intentionally small: a lending position plus a borrow gate.
-/
structure BorrowState where
  position : LendingPosition
  borrowPaused : Bool

/-- Position update induced by a successful borrow of `amount`. -/
def borrowPosition (position : LendingPosition) (amount : Rat) : LendingPosition :=
  { position with debt := position.debt + amount }

/-- Set the borrow gate to paused without changing the position. -/
def pauseBorrow (state : BorrowState) : BorrowState :=
  { state with borrowPaused := true }

/--
Apply a borrow transition. When the state is paused, the transition fails
closed and leaves the state unchanged.
-/
def applyBorrow (state : BorrowState) (amount : Rat) : BorrowState :=
  if state.borrowPaused then
    state
  else
    { position := borrowPosition state.position amount
      borrowPaused := state.borrowPaused }

/--
Worst-case borrow headroom under the adverse oracle price.

If `amount ≤ adverseBorrowHeadroom`, then borrowing `amount` keeps debt below the
worst-case max-safe-debt threshold.
-/
def adverseBorrowHeadroom (bounds : OracleBounds) (position : LendingPosition) : Rat :=
  maxSafeDebt position (adversePrice bounds) - position.debt

theorem pauseBorrow_sets_flag
    (state : BorrowState) :
    (pauseBorrow state).borrowPaused = true := by
  rfl

theorem pauseBorrow_preserves_position
    (state : BorrowState) :
    (pauseBorrow state).position = state.position := by
  rfl

theorem applyBorrow_eq_self_of_paused
    (state : BorrowState)
    (amount : Rat)
    (hPaused : state.borrowPaused = true) :
    applyBorrow state amount = state := by
  simp [applyBorrow, hPaused]

theorem applyBorrow_position_eq_borrowPosition_of_not_paused
    (state : BorrowState)
    (amount : Rat)
    (hPaused : state.borrowPaused = false) :
    (applyBorrow state amount).position = borrowPosition state.position amount := by
  simp [applyBorrow, hPaused, borrowPosition]

theorem applyBorrow_preserves_gate_of_not_paused
    (state : BorrowState)
    (amount : Rat)
    (hPaused : state.borrowPaused = false) :
    (applyBorrow state amount).borrowPaused = false := by
  simp [applyBorrow, hPaused]

theorem borrowPosition_collateral
    (position : LendingPosition)
    (amount : Rat) :
    (borrowPosition position amount).collateral = position.collateral := by
  rfl

theorem borrowPosition_threshold
    (position : LendingPosition)
    (amount : Rat) :
    (borrowPosition position amount).liquidationThreshold = position.liquidationThreshold := by
  rfl

theorem borrowPosition_debt
    (position : LendingPosition)
    (amount : Rat) :
    (borrowPosition position amount).debt = position.debt + amount := by
  rfl

theorem maxSafeDebt_borrowPosition_eq
    (position : LendingPosition)
    (amount price : Rat) :
    maxSafeDebt (borrowPosition position amount) price = maxSafeDebt position price := by
  rfl

theorem adverseBorrowHeadroom_nonneg_of_solventAt_adverse
    (position : LendingPosition)
    (bounds : OracleBounds)
    (hThreshold : 0 < position.liquidationThreshold)
    (hSolvent : solventAt position (adversePrice bounds)) :
    0 ≤ adverseBorrowHeadroom bounds position := by
  dsimp [adverseBorrowHeadroom]
  exact sub_nonneg.mpr
    ((debt_le_maxSafeDebt_iff position (adversePrice bounds) hThreshold).2 hSolvent)

theorem borrowPosition_debt_le_maxSafeDebt_of_le_adverseHeadroom
    (position : LendingPosition)
    (bounds : OracleBounds)
    (amount : Rat)
    (hAmount : amount ≤ adverseBorrowHeadroom bounds position) :
    (borrowPosition position amount).debt ≤
      maxSafeDebt (borrowPosition position amount) (adversePrice bounds) := by
  have hCap : position.debt + amount ≤ maxSafeDebt position (adversePrice bounds) := by
    dsimp [adverseBorrowHeadroom] at hAmount
    linarith
  simpa [borrowPosition, maxSafeDebt_borrowPosition_eq] using hCap

theorem solventAt_adverse_of_borrowWithinHeadroom
    (position : LendingPosition)
    (bounds : OracleBounds)
    (amount : Rat)
    (hThreshold : 0 < position.liquidationThreshold)
    (hAmount : amount ≤ adverseBorrowHeadroom bounds position) :
    solventAt (borrowPosition position amount) (adversePrice bounds) := by
  exact
    (debt_le_maxSafeDebt_iff
      (borrowPosition position amount)
      (adversePrice bounds)
      (by simpa [borrowPosition_threshold] using hThreshold)).1
      (borrowPosition_debt_le_maxSafeDebt_of_le_adverseHeadroom position bounds amount hAmount)

theorem solventAt_of_borrowWithinHeadroom_inOracleEnvelope
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (amount : Rat)
    (hThreshold : 0 < position.liquidationThreshold)
    (hCollateral : 0 ≤ position.collateral)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hAmount : amount ≤ adverseBorrowHeadroom bounds position) :
    solventAt (borrowPosition position amount) actualPrice := by
  have hAdverse :
      solventAt (borrowPosition position amount) (adversePrice bounds) :=
    solventAt_adverse_of_borrowWithinHeadroom position bounds amount hThreshold hAmount
  have hCollateral' : 0 ≤ (borrowPosition position amount).collateral := by
    simpa [borrowPosition_collateral] using hCollateral
  exact solventAt_of_inOracleEnvelope
    (borrowPosition position amount)
    bounds
    hCollateral'
    hEnvelope
    hAdverse

theorem solventAt_position_of_applyBorrow_withinHeadroom_inOracleEnvelope
    (state : BorrowState)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (amount : Rat)
    (hPaused : state.borrowPaused = false)
    (hThreshold : 0 < state.position.liquidationThreshold)
    (hCollateral : 0 ≤ state.position.collateral)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hAmount : amount ≤ adverseBorrowHeadroom bounds state.position) :
    solventAt (applyBorrow state amount).position actualPrice := by
  rw [applyBorrow_position_eq_borrowPosition_of_not_paused state amount hPaused]
  exact solventAt_of_borrowWithinHeadroom_inOracleEnvelope
    state.position bounds amount hThreshold hCollateral hEnvelope hAmount

end LeanMathlib
