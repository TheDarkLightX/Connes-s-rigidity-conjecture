import Mathlib
import LeanMathlib.DeFi.SimplexBorrowCoreOps

namespace LeanMathlib

theorem borrowCoreV0OpenAGuard_implies_troveA_noBadDebt
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenAGuard state collIn debtOut) :
    troveNoBadDebt (openA state collIn debtOut).troveA borrowCoreV0Params.priceCents := by
  rcases hGuard with ⟨_, _, hMin, _, _, hMcr⟩
  have hDebtOut : 0 ≤ debtOut := by
    norm_num [borrowCoreV0Params] at hMin
    linarith
  exact troveNoBadDebt_of_mcrOkAtQuotedPrice
    { collateral := collIn, debt := debtOut }
    hDebtOut
    hMcr

theorem borrowCoreV0BorrowMoreAGuard_implies_troveA_noBadDebt
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hGuard : borrowCoreV0BorrowMoreAGuard state extraDebt) :
    troveNoBadDebt (borrowMoreA state extraDebt).troveA borrowCoreV0Params.priceCents := by
  rcases hGuard with ⟨hDebt, hExtra, _, _, hMcr⟩
  have hDebtNonneg : 0 ≤ state.troveA.debt + extraDebt := by
    linarith
  exact troveNoBadDebt_of_mcrOkAtQuotedPrice
    { state.troveA with debt := state.troveA.debt + extraDebt }
    hDebtNonneg
    hMcr

theorem borrowCoreV0OpenAGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenAGuard state collIn debtOut)
    (hB : troveNoBadDebt state.troveB borrowCoreV0Params.priceCents)
    (hSp : 0 ≤ state.spColl) :
    systemNoBadDebt (openA state collIn debtOut) borrowCoreV0Params.priceCents := by
  have hA' :
      troveNoBadDebt (openA state collIn debtOut).troveA borrowCoreV0Params.priceCents := by
    exact borrowCoreV0OpenAGuard_implies_troveA_noBadDebt state collIn debtOut hGuard
  have hB' :
      troveNoBadDebt (openA state collIn debtOut).troveB borrowCoreV0Params.priceCents := by
    simpa [openA] using hB
  have hSp' : 0 ≤ (openA state collIn debtOut).spColl := by
    simpa [openA] using hSp
  have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
    norm_num [borrowCoreV0Params]
  exact systemNoBadDebt_of_trovesNoBadDebt (openA state collIn debtOut) hA' hB' hSp' hPrice

theorem borrowCoreV0OpenBGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hGuard : borrowCoreV0OpenBGuard state collIn debtOut)
    (hA : troveNoBadDebt state.troveA borrowCoreV0Params.priceCents)
    (hSp : 0 ≤ state.spColl) :
    systemNoBadDebt (openB state collIn debtOut) borrowCoreV0Params.priceCents := by
  have hA' :
      troveNoBadDebt (openB state collIn debtOut).troveA borrowCoreV0Params.priceCents := by
    simpa [openB] using hA
  have hB' :
      troveNoBadDebt (openB state collIn debtOut).troveB borrowCoreV0Params.priceCents := by
    exact borrowCoreV0OpenBGuard_implies_troveB_noBadDebt state collIn debtOut hGuard
  have hSp' : 0 ≤ (openB state collIn debtOut).spColl := by
    simpa [openB] using hSp
  have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
    norm_num [borrowCoreV0Params]
  exact systemNoBadDebt_of_trovesNoBadDebt (openB state collIn debtOut) hA' hB' hSp' hPrice

theorem borrowCoreV0BorrowMoreAGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hGuard : borrowCoreV0BorrowMoreAGuard state extraDebt)
    (hB : troveNoBadDebt state.troveB borrowCoreV0Params.priceCents)
    (hSp : 0 ≤ state.spColl) :
    systemNoBadDebt (borrowMoreA state extraDebt) borrowCoreV0Params.priceCents := by
  have hA' :
      troveNoBadDebt (borrowMoreA state extraDebt).troveA borrowCoreV0Params.priceCents := by
    exact borrowCoreV0BorrowMoreAGuard_implies_troveA_noBadDebt state extraDebt hGuard
  have hB' :
      troveNoBadDebt (borrowMoreA state extraDebt).troveB borrowCoreV0Params.priceCents := by
    simpa [borrowMoreA] using hB
  have hSp' : 0 ≤ (borrowMoreA state extraDebt).spColl := by
    simpa [borrowMoreA] using hSp
  have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
    norm_num [borrowCoreV0Params]
  exact systemNoBadDebt_of_trovesNoBadDebt (borrowMoreA state extraDebt) hA' hB' hSp' hPrice

theorem borrowCoreV0RepayAGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : borrowCoreV0RepayAGuard state amt)
    (hSystem : systemNoBadDebt state borrowCoreV0Params.priceCents) :
    systemNoBadDebt (repayA state amt) borrowCoreV0Params.priceCents := by
  exact borrowCoreV0RepayAGuard_preserves_systemNoBadDebt state amt hGuard hSystem

theorem borrowCoreV0WithdrawCollAGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hState : borrowCoreV0StateNonneg state)
    (hGuard : borrowCoreV0WithdrawCollAGuard state amt)
    (hB : troveNoBadDebt state.troveB borrowCoreV0Params.priceCents)
    (hSp : 0 ≤ state.spColl) :
    systemNoBadDebt (withdrawCollA state amt) borrowCoreV0Params.priceCents := by
  have hA' :
      troveNoBadDebt (withdrawCollA state amt).troveA borrowCoreV0Params.priceCents := by
    exact borrowCoreV0WithdrawCollAGuard_implies_troveA_noBadDebt state amt hState hGuard
  have hB' :
      troveNoBadDebt (withdrawCollA state amt).troveB borrowCoreV0Params.priceCents := by
    simpa [withdrawCollA] using hB
  have hSp' : 0 ≤ (withdrawCollA state amt).spColl := by
    simpa [withdrawCollA] using hSp
  have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
    norm_num [borrowCoreV0Params]
  exact systemNoBadDebt_of_trovesNoBadDebt (withdrawCollA state amt) hA' hB' hSp' hPrice

theorem depositSP_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSystem : systemNoBadDebt state borrowCoreV0Params.priceCents) :
    systemNoBadDebt (depositSP state amt) borrowCoreV0Params.priceCents := by
  exact depositSP_preserves_systemNoBadDebt state amt hSystem

theorem withdrawSPGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (_hGuard : withdrawSPGuard state amt)
    (hSystem : systemNoBadDebt state borrowCoreV0Params.priceCents) :
    systemNoBadDebt (withdrawSP state amt) borrowCoreV0Params.priceCents := by
  exact withdrawSP_preserves_systemNoBadDebt state amt hSystem

theorem liquidateAGuard_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (hGuard : liquidateAGuard state)
    (hSystem : systemNoBadDebt state borrowCoreV0Params.priceCents) :
    systemNoBadDebt (liquidateA state) borrowCoreV0Params.priceCents := by
  exact liquidateA_preserves_systemNoBadDebt
    state
    hGuard.1.le
    hSystem

end LeanMathlib
