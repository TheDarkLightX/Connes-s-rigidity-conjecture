import Mathlib
import LeanMathlib.DeFi.SimplexBorrowCoreInvariants

namespace LeanMathlib

/-- Enumerated action surface for the arithmetic `borrow_core_v0` packet. -/
inductive BorrowCoreV0Action where
  | openA (collIn debtOut : Rat)
  | openB (collIn debtOut : Rat)
  | borrowMoreA (extraDebt : Rat)
  | repayA (amt : Rat)
  | withdrawCollA (amt : Rat)
  | depositSP (amt : Rat)
  | withdrawSP (amt : Rat)
  | liquidateA

/-- Deterministic state update for a single arithmetic `borrow_core_v0` action. -/
def stepAction (state : SimplexBorrowState) : BorrowCoreV0Action → SimplexBorrowState
  | .openA collIn debtOut => openA state collIn debtOut
  | .openB collIn debtOut => openB state collIn debtOut
  | .borrowMoreA extraDebt => borrowMoreA state extraDebt
  | .repayA amt => repayA state amt
  | .withdrawCollA amt => withdrawCollA state amt
  | .depositSP amt => depositSP state amt
  | .withdrawSP amt => withdrawSP state amt
  | .liquidateA => liquidateA state

/-- Enablement relation for the arithmetic `borrow_core_v0` action packet. -/
def actionEnabled (state : SimplexBorrowState) : BorrowCoreV0Action → Prop
  | .openA collIn debtOut => borrowCoreV0OpenAGuard state collIn debtOut
  | .openB collIn debtOut => borrowCoreV0OpenBGuard state collIn debtOut
  | .borrowMoreA extraDebt => borrowCoreV0BorrowMoreAGuard state extraDebt
  | .repayA amt => borrowCoreV0RepayAGuard state amt
  | .withdrawCollA amt => borrowCoreV0WithdrawCollAGuard state amt
  | .depositSP amt => depositSPGuard state amt
  | .withdrawSP amt => withdrawSPGuard state amt
  | .liquidateA => liquidateAGuard state

/--
Quoted-price invariant bundle for the arithmetic `borrow_core_v0` surface:
supply conservation, both troves individually free of bad debt, and
nonnegative stability-pool collateral.
-/
def quotedInvariantState (state : SimplexBorrowState) : Prop :=
  supplyConservation state ∧
    troveNoBadDebt state.troveA borrowCoreV0Params.priceCents ∧
    troveNoBadDebt state.troveB borrowCoreV0Params.priceCents ∧
    0 ≤ state.spColl

theorem quotedInvariantState_implies_systemNoBadDebt
    (state : SimplexBorrowState)
    (hInv : quotedInvariantState state) :
    systemNoBadDebt state borrowCoreV0Params.priceCents := by
  rcases hInv with ⟨_, hA, hB, hSp⟩
  have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
    norm_num [borrowCoreV0Params]
  exact systemNoBadDebt_of_trovesNoBadDebt state hA hB hSp hPrice

theorem borrowCoreV0RepayAGuard_preserves_troveA_noBadDebt
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : borrowCoreV0RepayAGuard state amt)
    (hA : troveNoBadDebt state.troveA borrowCoreV0Params.priceCents) :
    troveNoBadDebt (repayA state amt).troveA borrowCoreV0Params.priceCents := by
  dsimp [troveNoBadDebt, repayA] at hA ⊢
  have hDebtLe : state.troveA.debt - amt ≤ state.troveA.debt := by
    exact sub_le_self _ hGuard.1.le
  exact le_trans hDebtLe hA

theorem liquidateAGuard_and_troveANoBadDebt_imply_troveACollateral_nonneg
    (state : SimplexBorrowState)
    (hGuard : liquidateAGuard state)
    (hA : troveNoBadDebt state.troveA borrowCoreV0Params.priceCents) :
    0 ≤ state.troveA.collateral := by
  dsimp [troveNoBadDebt] at hA
  have hValuePos : 0 < state.troveA.collateral * borrowCoreV0Params.priceCents := by
    exact lt_of_lt_of_le hGuard.1 hA
  have hPrice : 0 < borrowCoreV0Params.priceCents := by
    norm_num [borrowCoreV0Params]
  nlinarith

theorem borrowCoreV0WithdrawCollAGuard_preserves_troveA_noBadDebt
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : borrowCoreV0WithdrawCollAGuard state amt) :
    troveNoBadDebt (withdrawCollA state amt).troveA borrowCoreV0Params.priceCents := by
  rcases hGuard with ⟨_, hAmtLe, hOk⟩
  rcases hOk with hDebt0 | hMcr
  · have hCollNonneg : 0 ≤ state.troveA.collateral - amt := sub_nonneg.mpr hAmtLe
    have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
      norm_num [borrowCoreV0Params]
    dsimp [troveNoBadDebt, withdrawCollA]
    rw [hDebt0]
    have hValueNonneg :
        0 ≤ (state.troveA.collateral - amt) * borrowCoreV0Params.priceCents := by
      exact mul_nonneg hCollNonneg hPrice
    nlinarith
  · have hCollNonneg : 0 ≤ state.troveA.collateral - amt := sub_nonneg.mpr hAmtLe
    dsimp [troveNoBadDebt, withdrawCollA, mcrOkAtQuotedPrice] at hMcr ⊢
    norm_num [borrowCoreV0Params] at hMcr ⊢
    nlinarith

theorem actionEnabled_preserves_quotedInvariantState
    (state : SimplexBorrowState)
    (action : BorrowCoreV0Action)
    (hInv : quotedInvariantState state)
    (hEnabled : actionEnabled state action) :
    quotedInvariantState (stepAction state action) := by
  rcases hInv with ⟨hSupply, hA, hB, hSp⟩
  cases action with
  | openA collIn debtOut =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact openA_preserves_supplyConservation state collIn debtOut hSupply hEnabled.1
      · exact borrowCoreV0OpenAGuard_implies_troveA_noBadDebt state collIn debtOut hEnabled
      · simpa [openA] using hB
      · simpa [openA] using hSp
  | openB collIn debtOut =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact openB_preserves_supplyConservation state collIn debtOut hSupply hEnabled.1
      · simpa [openB] using hA
      · exact borrowCoreV0OpenBGuard_implies_troveB_noBadDebt state collIn debtOut hEnabled
      · simpa [openB] using hSp
  | borrowMoreA extraDebt =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact borrowMoreA_preserves_supplyConservation state extraDebt hSupply
      · exact borrowCoreV0BorrowMoreAGuard_implies_troveA_noBadDebt state extraDebt hEnabled
      · simpa [borrowMoreA] using hB
      · simpa [borrowMoreA] using hSp
  | repayA amt =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact repayA_preserves_supplyConservation state amt hSupply
      · exact borrowCoreV0RepayAGuard_preserves_troveA_noBadDebt state amt hEnabled hA
      · simpa [repayA] using hB
      · simpa [repayA] using hSp
  | withdrawCollA amt =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact withdrawCollA_preserves_supplyConservation state amt hSupply
      · exact borrowCoreV0WithdrawCollAGuard_preserves_troveA_noBadDebt state amt hEnabled
      · simpa [withdrawCollA] using hB
      · simpa [withdrawCollA] using hSp
  | depositSP amt =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact depositSP_preserves_supplyConservation state amt hSupply
      · simpa [depositSP] using hA
      · simpa [depositSP] using hB
      · simpa [depositSP] using hSp
  | withdrawSP amt =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact withdrawSP_preserves_supplyConservation state amt hSupply
      · simpa [withdrawSP] using hA
      · simpa [withdrawSP] using hB
      · simpa [withdrawSP] using hSp
  | liquidateA =>
      dsimp [actionEnabled, stepAction] at hEnabled ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact liquidateA_preserves_supplyConservation state hSupply
      · norm_num [troveNoBadDebt, liquidateA]
      · simpa [liquidateA] using hB
      · have hAColl : 0 ≤ state.troveA.collateral := by
          exact liquidateAGuard_and_troveANoBadDebt_imply_troveACollateral_nonneg state hEnabled hA
        dsimp [liquidateA]
        linarith

theorem actionEnabled_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (action : BorrowCoreV0Action)
    (hInv : quotedInvariantState state)
    (hEnabled : actionEnabled state action) :
    systemNoBadDebt (stepAction state action) borrowCoreV0Params.priceCents := by
  exact quotedInvariantState_implies_systemNoBadDebt
    (stepAction state action)
    (actionEnabled_preserves_quotedInvariantState state action hInv hEnabled)

end LeanMathlib
