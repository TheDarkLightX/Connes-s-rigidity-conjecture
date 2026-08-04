import Mathlib
import LeanMathlib.DeFi.SimplexBorrowStabilityPool

namespace LeanMathlib

/-- `open_b` transition from the local functional core. -/
def openB (state : SimplexBorrowState) (collIn debtOut : Rat) : SimplexBorrowState :=
  { state with
    troveB := { collateral := collIn, debt := debtOut }
    freeDebt := state.freeDebt + debtOut }

/-- `repay_a` transition from the local functional core. -/
def repayA (state : SimplexBorrowState) (amt : Rat) : SimplexBorrowState :=
  { state with
    troveA := { state.troveA with debt := state.troveA.debt - amt }
    freeDebt := state.freeDebt - amt }

/-- `withdraw_coll_a` transition from the local functional core. -/
def withdrawCollA (state : SimplexBorrowState) (amt : Rat) : SimplexBorrowState :=
  { state with
    troveA := { state.troveA with collateral := state.troveA.collateral - amt } }

/-- Python-style `open_b` guard. -/
def borrowCoreV0OpenBGuard
    (state : SimplexBorrowState)
    (collIn debtOut : Rat) : Prop :=
  state.troveB.debt = 0 ∧
    state.troveB.collateral = 0 ∧
    borrowCoreV0Params.minDebtOpen ≤ debtOut ∧
    state.freeDebt + debtOut ≤ borrowCoreV0Params.maxDebtSupply ∧
    debtOut ≤ borrowCoreV0Params.maxDebt ∧
    mcrOkAtQuotedPrice borrowCoreV0Params { collateral := collIn, debt := debtOut }

/-- Python-style `repay_a` guard. -/
def borrowCoreV0RepayAGuard
    (state : SimplexBorrowState)
    (amt : Rat) : Prop :=
  0 < amt ∧
    amt ≤ state.troveA.debt ∧
    amt ≤ state.freeDebt

/-- Python-style `withdraw_coll_a` guard. -/
def borrowCoreV0WithdrawCollAGuard
    (state : SimplexBorrowState)
    (amt : Rat) : Prop :=
  0 < amt ∧
    amt ≤ state.troveA.collateral ∧
    (state.troveA.debt = 0 ∨
      mcrOkAtQuotedPrice
        borrowCoreV0Params
        { state.troveA with collateral := state.troveA.collateral - amt })

theorem troveNoBadDebt_of_mcrOkAtQuotedPrice
    (trove : SimplexTrove)
    (hDebt : 0 ≤ trove.debt)
    (hMcr : mcrOkAtQuotedPrice borrowCoreV0Params trove) :
    troveNoBadDebt trove borrowCoreV0Params.priceCents := by
  dsimp [troveNoBadDebt, mcrOkAtQuotedPrice] at *
  norm_num [borrowCoreV0Params] at hMcr ⊢
  nlinarith

theorem openB_preserves_supplyConservation
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hSupply : supplyConservation state)
    (hOpen : state.troveB.debt = 0) :
    supplyConservation (openB state collIn debtOut) := by
  dsimp [supplyConservation, openB] at *
  linarith

theorem borrowCoreV0OpenBGuard_preserves_supplyConservation
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hSupply : supplyConservation state)
    (hGuard : borrowCoreV0OpenBGuard state collIn debtOut) :
    supplyConservation (openB state collIn debtOut) := by
  exact openB_preserves_supplyConservation state collIn debtOut hSupply hGuard.1

theorem borrowCoreV0OpenBGuard_implies_troveB_solventAt_quoted
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenBGuard state collIn debtOut) :
    solventAt (trovePosition borrowCoreV0Params (openB state collIn debtOut).troveB)
      borrowCoreV0Params.priceCents := by
  exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
    borrowCoreV0Params
    { collateral := collIn, debt := debtOut }
    borrowCoreV0Params_mcrDen_pos).2 hGuard.2.2.2.2.2

theorem borrowCoreV0OpenBGuard_implies_troveB_noBadDebt
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenBGuard state collIn debtOut) :
    troveNoBadDebt (openB state collIn debtOut).troveB borrowCoreV0Params.priceCents := by
  have hDebtOut : 0 ≤ debtOut := by
    have hMin := hGuard.2.2.1
    norm_num [borrowCoreV0Params] at hMin
    linarith
  exact troveNoBadDebt_of_mcrOkAtQuotedPrice
    { collateral := collIn, debt := debtOut }
    hDebtOut
    hGuard.2.2.2.2.2

theorem repayA_preserves_supplyConservation
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSupply : supplyConservation state) :
    supplyConservation (repayA state amt) := by
  dsimp [supplyConservation, repayA] at *
  linarith

theorem borrowCoreV0RepayAGuard_preserves_supplyConservation
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSupply : supplyConservation state)
    (_hGuard : borrowCoreV0RepayAGuard state amt) :
    supplyConservation (repayA state amt) := by
  exact repayA_preserves_supplyConservation state amt hSupply

theorem borrowCoreV0RepayAGuard_preserves_troveA_solventAt_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : borrowCoreV0RepayAGuard state amt)
    (hSolvent :
      solventAt (trovePosition borrowCoreV0Params state.troveA)
        borrowCoreV0Params.priceCents) :
    solventAt (trovePosition borrowCoreV0Params (repayA state amt).troveA)
      borrowCoreV0Params.priceCents := by
  have hMcr :
      mcrOkAtQuotedPrice borrowCoreV0Params state.troveA := by
    exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
      borrowCoreV0Params
      state.troveA
      borrowCoreV0Params_mcrDen_pos).1 hSolvent
  have hScaled :
      (state.troveA.debt - amt) * borrowCoreV0Params.mcrNum ≤
        state.troveA.debt * borrowCoreV0Params.mcrNum := by
    have hDebtLe : state.troveA.debt - amt ≤ state.troveA.debt := by
      exact sub_le_self _ hGuard.1.le
    exact mul_le_mul_of_nonneg_right hDebtLe borrowCoreV0Params_mcrNum_pos.le
  have hMcr' :
      mcrOkAtQuotedPrice
        borrowCoreV0Params
        { state.troveA with debt := state.troveA.debt - amt } := by
    dsimp [mcrOkAtQuotedPrice] at hMcr ⊢
    exact le_trans hScaled hMcr
  exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
    borrowCoreV0Params
    { state.troveA with debt := state.troveA.debt - amt }
    borrowCoreV0Params_mcrDen_pos).2 hMcr'

theorem borrowCoreV0RepayAGuard_preserves_systemNoBadDebt
    (state : SimplexBorrowState)
    {price : Rat}
    (amt : Rat)
    (hGuard : borrowCoreV0RepayAGuard state amt)
    (hSystem : systemNoBadDebt state price) :
    systemNoBadDebt (repayA state amt) price := by
  have hDebt :
      systemTroveDebt (repayA state amt) ≤ systemTroveDebt state := by
    dsimp [systemTroveDebt, repayA]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right (sub_le_self state.troveA.debt hGuard.1.le) state.troveB.debt
  calc
    systemTroveDebt (repayA state amt)
      ≤ systemTroveDebt state := hDebt
    _ ≤ systemCollateralValue state price := hSystem
    _ = systemCollateralValue (repayA state amt) price := by
      rfl

theorem withdrawCollA_preserves_supplyConservation
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSupply : supplyConservation state) :
    supplyConservation (withdrawCollA state amt) := by
  simpa [supplyConservation, withdrawCollA] using hSupply

theorem borrowCoreV0WithdrawCollAGuard_preserves_supplyConservation
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSupply : supplyConservation state)
    (_hGuard : borrowCoreV0WithdrawCollAGuard state amt) :
    supplyConservation (withdrawCollA state amt) := by
  exact withdrawCollA_preserves_supplyConservation state amt hSupply

theorem borrowCoreV0WithdrawCollAGuard_implies_troveA_solventAt_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : borrowCoreV0WithdrawCollAGuard state amt) :
    solventAt (trovePosition borrowCoreV0Params (withdrawCollA state amt).troveA)
      borrowCoreV0Params.priceCents := by
  rcases hGuard with ⟨hAmtPos, hAmtLe, hOk⟩
  rcases hOk with hDebt0 | hMcr
  · have hCollNonneg : 0 ≤ state.troveA.collateral - amt := sub_nonneg.mpr hAmtLe
    have hValueNonneg :
        0 ≤ (state.troveA.collateral - amt) * borrowCoreV0Params.priceCents := by
      have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
        norm_num [borrowCoreV0Params]
      exact mul_nonneg hCollNonneg hPrice
    dsimp [solventAt, collateralValue, trovePosition, mcrThreshold, withdrawCollA]
    rw [hDebt0]
    nlinarith
  · exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
      borrowCoreV0Params
      { state.troveA with collateral := state.troveA.collateral - amt }
      borrowCoreV0Params_mcrDen_pos).2 hMcr

theorem borrowCoreV0WithdrawCollAGuard_implies_troveA_noBadDebt
    (state : SimplexBorrowState)
    (amt : Rat)
    (hState : borrowCoreV0StateNonneg state)
    (hGuard : borrowCoreV0WithdrawCollAGuard state amt) :
    troveNoBadDebt (withdrawCollA state amt).troveA borrowCoreV0Params.priceCents := by
  rcases hState with ⟨_, hDebtNonneg, _, _, _, _, _⟩
  rcases hGuard with ⟨hAmtPos, hAmtLe, hOk⟩
  rcases hOk with hDebt0 | hMcr
  · have hCollNonneg : 0 ≤ state.troveA.collateral - amt := sub_nonneg.mpr hAmtLe
    have hValueNonneg :
        0 ≤ (state.troveA.collateral - amt) * borrowCoreV0Params.priceCents := by
      have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
        norm_num [borrowCoreV0Params]
      exact mul_nonneg hCollNonneg hPrice
    dsimp [troveNoBadDebt, withdrawCollA]
    rw [hDebt0]
    nlinarith
  · exact troveNoBadDebt_of_mcrOkAtQuotedPrice
      { state.troveA with collateral := state.troveA.collateral - amt }
      hDebtNonneg
      hMcr

end LeanMathlib
