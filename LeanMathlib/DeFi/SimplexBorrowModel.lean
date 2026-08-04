import Mathlib
import LeanMathlib.DeFi.BorrowPause

namespace LeanMathlib

/--
Minimal trove model aligned to the local `SimplexBorrow` functional core.
-/
structure SimplexTrove where
  collateral : Rat
  debt : Rat

/--
Borrow-core parameters aligned to the local `borrow_core_v0` style surface.
-/
structure SimplexBorrowParams where
  priceCents : Rat
  mcrNum : Rat
  mcrDen : Rat
  maxDebt : Rat
  minDebtOpen : Rat
  maxDebtSupply : Rat

/-- The liquidation threshold induced by the MCR fraction. -/
def mcrThreshold (params : SimplexBorrowParams) : Rat :=
  params.mcrNum / params.mcrDen

/-- Oracle bounds with quoted price equal to the model's current price. -/
def quotedBounds (params : SimplexBorrowParams) (maxDownwardDeviation : Rat) : OracleBounds :=
  { quotedPrice := params.priceCents
    maxDownwardDeviation := maxDownwardDeviation }

/-- Canonical local parameters matching `borrow_core_v0.py`. -/
def borrowCoreV0Params : SimplexBorrowParams :=
  { priceCents := 100
    mcrNum := 11
    mcrDen := 10
    maxDebt := 2000
    minDebtOpen := 100
    maxDebtSupply := 4000 }

/--
Borrow-core state mirroring the local `SimplexBorrow` functional core at a
minimal arithmetic level.
-/
structure SimplexBorrowState where
  troveA : SimplexTrove
  troveB : SimplexTrove
  freeDebt : Rat
  spDebt : Rat
  spColl : Rat

/-- Map a trove into the generic lending-position surface. -/
def trovePosition (params : SimplexBorrowParams) (trove : SimplexTrove) : LendingPosition :=
  { collateral := trove.collateral
    debt := trove.debt
    liquidationThreshold := mcrThreshold params }

/-- Supply conservation predicate used in the local borrow core. -/
def supplyConservation (state : SimplexBorrowState) : Prop :=
  state.freeDebt + state.spDebt = state.troveA.debt + state.troveB.debt

/-- `open_a` style transition. -/
def openA (state : SimplexBorrowState) (collIn debtOut : Rat) : SimplexBorrowState :=
  { state with
    troveA := { collateral := collIn, debt := debtOut }
    freeDebt := state.freeDebt + debtOut }

/-- `borrow_more_a` style transition. -/
def borrowMoreA (state : SimplexBorrowState) (extraDebt : Rat) : SimplexBorrowState :=
  { state with
    troveA := { state.troveA with debt := state.troveA.debt + extraDebt }
    freeDebt := state.freeDebt + extraDebt }

/-- Guard for the `open_a` transition. -/
def openAGuard
    (params : SimplexBorrowParams)
    (state : SimplexBorrowState)
    (collIn debtOut : Rat) : Prop :=
  state.troveA.debt = 0 ∧
    state.troveA.collateral = 0 ∧
    params.minDebtOpen ≤ debtOut ∧
    state.freeDebt + debtOut ≤ params.maxDebtSupply ∧
    debtOut ≤ params.maxDebt ∧
    solventAt (trovePosition params { collateral := collIn, debt := debtOut }) params.priceCents

/-- Guard for the `borrow_more_a` transition. -/
def borrowMoreAGuard
    (params : SimplexBorrowParams)
    (state : SimplexBorrowState)
    (extraDebt : Rat) : Prop :=
  0 < state.troveA.debt ∧
    0 < extraDebt ∧
    state.freeDebt + extraDebt ≤ params.maxDebtSupply ∧
    state.troveA.debt + extraDebt ≤ params.maxDebt ∧
    solventAt
      (trovePosition params
        { state.troveA with debt := state.troveA.debt + extraDebt })
      params.priceCents

theorem trovePosition_borrowMoreA_eq_borrowPosition
    (params : SimplexBorrowParams)
    (state : SimplexBorrowState)
    (extraDebt : Rat) :
    trovePosition params (borrowMoreA state extraDebt).troveA =
      borrowPosition (trovePosition params state.troveA) extraDebt := by
  rfl

theorem mcrThreshold_pos
    (params : SimplexBorrowParams)
    (hNum : 0 < params.mcrNum)
    (hDen : 0 < params.mcrDen) :
    0 < mcrThreshold params := by
  dsimp [mcrThreshold]
  exact div_pos hNum hDen

theorem openA_preserves_supplyConservation
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hSupply : supplyConservation state)
    (hOpen : state.troveA.debt = 0) :
    supplyConservation (openA state collIn debtOut) := by
  dsimp [supplyConservation, openA] at *
  linarith

theorem borrowMoreA_preserves_supplyConservation
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hSupply : supplyConservation state) :
    supplyConservation (borrowMoreA state extraDebt) := by
  dsimp [supplyConservation, borrowMoreA] at *
  linarith

theorem openAGuard_implies_solventAt_quoted
    (params : SimplexBorrowParams)
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : openAGuard params state collIn debtOut) :
    solventAt (trovePosition params (openA state collIn debtOut).troveA) params.priceCents := by
  exact hGuard.2.2.2.2.2

theorem borrowMoreAGuard_implies_solventAt_quoted
    (params : SimplexBorrowParams)
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hGuard : borrowMoreAGuard params state extraDebt) :
    solventAt (trovePosition params (borrowMoreA state extraDebt).troveA) params.priceCents := by
  exact hGuard.2.2.2.2

theorem borrowMoreA_solventAt_inOracleEnvelope_of_headroom
    (params : SimplexBorrowParams)
    (state : SimplexBorrowState)
    (maxDownwardDeviation : Rat)
    {actualPrice : Rat}
    (extraDebt : Rat)
    (hNum : 0 < params.mcrNum)
    (hDen : 0 < params.mcrDen)
    (hCollateral : 0 ≤ state.troveA.collateral)
    (hEnvelope : inOracleEnvelope (quotedBounds params maxDownwardDeviation) actualPrice)
    (hAmount :
      extraDebt ≤ adverseBorrowHeadroom
        (quotedBounds params maxDownwardDeviation)
        (trovePosition params state.troveA)) :
    solventAt (trovePosition params (borrowMoreA state extraDebt).troveA) actualPrice := by
  have hThreshold : 0 < (trovePosition params state.troveA).liquidationThreshold := by
    simpa [trovePosition] using mcrThreshold_pos params hNum hDen
  have hBorrow :
      solventAt
        (applyBorrow
          { position := trovePosition params state.troveA
            borrowPaused := false }
          extraDebt).position
        actualPrice := by
    exact solventAt_position_of_applyBorrow_withinHeadroom_inOracleEnvelope
      { position := trovePosition params state.troveA
        borrowPaused := false }
      (quotedBounds params maxDownwardDeviation)
      extraDebt
      rfl
      hThreshold
      (by simpa [trovePosition] using hCollateral)
      hEnvelope
      hAmount
  simpa [applyBorrow, trovePosition_borrowMoreA_eq_borrowPosition, borrowMoreA] using hBorrow

end LeanMathlib
