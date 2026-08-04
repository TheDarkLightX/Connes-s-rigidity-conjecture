import Mathlib
import LeanMathlib.DeFi.SimplexBorrowModel

namespace LeanMathlib

/--
Cross-multiplication MCR check aligned to the local Python helper
`is_cr_at_least_mcr`.
-/
def mcrOkAtQuotedPrice (params : SimplexBorrowParams) (trove : SimplexTrove) : Prop :=
  trove.debt * params.mcrNum ≤ trove.collateral * params.priceCents * params.mcrDen

/--
Nonnegativity discipline aligned to the bounded integer state space in the local
functional core.
-/
def borrowCoreV0StateNonneg (state : SimplexBorrowState) : Prop :=
  0 ≤ state.troveA.collateral ∧
    0 ≤ state.troveA.debt ∧
    0 ≤ state.troveB.collateral ∧
    0 ≤ state.troveB.debt ∧
    0 ≤ state.freeDebt ∧
    0 ≤ state.spDebt ∧
    0 ≤ state.spColl

/-- `open_a` guard written in the same cross-multiplication style as the Python core. -/
def borrowCoreV0OpenAGuard
    (state : SimplexBorrowState)
    (collIn debtOut : Rat) : Prop :=
  state.troveA.debt = 0 ∧
    state.troveA.collateral = 0 ∧
    borrowCoreV0Params.minDebtOpen ≤ debtOut ∧
    state.freeDebt + debtOut ≤ borrowCoreV0Params.maxDebtSupply ∧
    debtOut ≤ borrowCoreV0Params.maxDebt ∧
    mcrOkAtQuotedPrice borrowCoreV0Params { collateral := collIn, debt := debtOut }

/-- `borrow_more_a` guard written in the same cross-multiplication style as the Python core. -/
def borrowCoreV0BorrowMoreAGuard
    (state : SimplexBorrowState)
    (extraDebt : Rat) : Prop :=
  0 < state.troveA.debt ∧
    0 < extraDebt ∧
    state.freeDebt + extraDebt ≤ borrowCoreV0Params.maxDebtSupply ∧
    state.troveA.debt + extraDebt ≤ borrowCoreV0Params.maxDebt ∧
    mcrOkAtQuotedPrice
      borrowCoreV0Params
      { state.troveA with debt := state.troveA.debt + extraDebt }

theorem borrowCoreV0Params_mcrNum_pos : 0 < borrowCoreV0Params.mcrNum := by
  norm_num [borrowCoreV0Params]

theorem borrowCoreV0Params_mcrDen_pos : 0 < borrowCoreV0Params.mcrDen := by
  norm_num [borrowCoreV0Params]

theorem solventAt_quoted_iff_mcrOkAtQuotedPrice
    (params : SimplexBorrowParams)
    (trove : SimplexTrove)
    (hDen : 0 < params.mcrDen) :
    solventAt (trovePosition params trove) params.priceCents ↔
      mcrOkAtQuotedPrice params trove := by
  constructor
  · intro h
    have h' :
        (trove.debt * params.mcrNum) / params.mcrDen ≤
          trove.collateral * params.priceCents := by
      simpa [solventAt, collateralValue, trovePosition, mcrThreshold,
        div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    exact (div_le_iff₀ hDen).1 <|
      by simpa [mcrOkAtQuotedPrice, mul_assoc, mul_left_comm, mul_comm] using h'
  · intro h
    have h' :
        (trove.debt * params.mcrNum) / params.mcrDen ≤
          trove.collateral * params.priceCents := by
      exact (div_le_iff₀ hDen).2 h
    simpa [solventAt, collateralValue, trovePosition, mcrThreshold,
      mcrOkAtQuotedPrice, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h'

theorem borrowCoreV0OpenAGuard_implies_openAGuard
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenAGuard state collIn debtOut) :
    openAGuard borrowCoreV0Params state collIn debtOut := by
  rcases hGuard with ⟨hDebt0, hColl0, hMin, hSupply, hMax, hMcr⟩
  refine ⟨hDebt0, hColl0, hMin, hSupply, hMax, ?_⟩
  exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
    borrowCoreV0Params
    { collateral := collIn, debt := debtOut }
    borrowCoreV0Params_mcrDen_pos).2 hMcr

theorem borrowCoreV0OpenAGuard_implies_solventAt_quoted
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenAGuard state collIn debtOut) :
    solventAt (trovePosition borrowCoreV0Params (openA state collIn debtOut).troveA)
      borrowCoreV0Params.priceCents := by
  exact openAGuard_implies_solventAt_quoted
    borrowCoreV0Params state collIn debtOut
    (borrowCoreV0OpenAGuard_implies_openAGuard state collIn debtOut hGuard)

theorem borrowCoreV0BorrowMoreAGuard_implies_borrowMoreAGuard
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hGuard : borrowCoreV0BorrowMoreAGuard state extraDebt) :
    borrowMoreAGuard borrowCoreV0Params state extraDebt := by
  rcases hGuard with ⟨hDebt, hExtra, hSupply, hMax, hMcr⟩
  refine ⟨hDebt, hExtra, hSupply, hMax, ?_⟩
  exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
    borrowCoreV0Params
    { state.troveA with debt := state.troveA.debt + extraDebt }
    borrowCoreV0Params_mcrDen_pos).2 hMcr

theorem borrowCoreV0BorrowMoreAGuard_implies_solventAt_quoted
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hGuard : borrowCoreV0BorrowMoreAGuard state extraDebt) :
    solventAt
      (trovePosition borrowCoreV0Params (borrowMoreA state extraDebt).troveA)
      borrowCoreV0Params.priceCents := by
  exact borrowMoreAGuard_implies_solventAt_quoted
    borrowCoreV0Params state extraDebt
    (borrowCoreV0BorrowMoreAGuard_implies_borrowMoreAGuard state extraDebt hGuard)

theorem borrowCoreV0BorrowMoreA_solventAt_inOracleEnvelope_of_headroom
    (state : SimplexBorrowState)
    (maxDownwardDeviation : Rat)
    {actualPrice : Rat}
    (extraDebt : Rat)
    (hState : borrowCoreV0StateNonneg state)
    (hEnvelope :
      inOracleEnvelope
        (quotedBounds borrowCoreV0Params maxDownwardDeviation)
        actualPrice)
    (hAmount :
      extraDebt ≤ adverseBorrowHeadroom
        (quotedBounds borrowCoreV0Params maxDownwardDeviation)
        (trovePosition borrowCoreV0Params state.troveA)) :
    solventAt
      (trovePosition borrowCoreV0Params (borrowMoreA state extraDebt).troveA)
      actualPrice := by
  exact borrowMoreA_solventAt_inOracleEnvelope_of_headroom
    borrowCoreV0Params
    state
    maxDownwardDeviation
    extraDebt
    borrowCoreV0Params_mcrNum_pos
    borrowCoreV0Params_mcrDen_pos
    hState.1
    hEnvelope
    hAmount

end LeanMathlib
