import Mathlib
import LeanMathlib.DeFi.SimplexBorrowCoreTrace

namespace LeanMathlib

/-- Trove collateral cap from the local `borrow_core_v0` YAML/Python surface. -/
def borrowCoreV0MaxColl : Rat := 20

/--
State-range discipline aligned to the local Python `_check_state_types` envelope,
excluding the fixed `price_cents` field because the Lean model uses the pinned
parameter bundle instead of storing price in state.
-/
def borrowCoreV0StateBounds (state : SimplexBorrowState) : Prop :=
  0 ≤ state.troveA.collateral ∧
    state.troveA.collateral ≤ borrowCoreV0MaxColl ∧
    0 ≤ state.troveA.debt ∧
    state.troveA.debt ≤ borrowCoreV0Params.maxDebt ∧
    0 ≤ state.troveB.collateral ∧
    state.troveB.collateral ≤ borrowCoreV0MaxColl ∧
    0 ≤ state.troveB.debt ∧
    state.troveB.debt ≤ borrowCoreV0Params.maxDebt ∧
    0 ≤ state.freeDebt ∧
    state.freeDebt ≤ borrowCoreV0Params.maxDebtSupply ∧
    0 ≤ state.spDebt ∧
    state.spDebt ≤ borrowCoreV0Params.maxDebtSupply ∧
    0 ≤ state.spColl ∧
    state.spColl ≤ borrowCoreV0MaxSpColl

/--
Action enablement aligned more closely to the local Python/ESSO command surface.
This adds the explicit `coll_in` typing envelope for `open_a` / `open_b`.
-/
def pythonActionEnabled (state : SimplexBorrowState) : BorrowCoreV0Action → Prop
  | .openA collIn debtOut =>
      1 ≤ collIn ∧ collIn ≤ borrowCoreV0MaxColl ∧
        borrowCoreV0OpenAGuard state collIn debtOut
  | .openB collIn debtOut =>
      1 ≤ collIn ∧ collIn ≤ borrowCoreV0MaxColl ∧
        borrowCoreV0OpenBGuard state collIn debtOut
  | .borrowMoreA extraDebt => borrowCoreV0BorrowMoreAGuard state extraDebt
  | .repayA amt => borrowCoreV0RepayAGuard state amt
  | .withdrawCollA amt => borrowCoreV0WithdrawCollAGuard state amt
  | .depositSP amt => depositSPGuard state amt
  | .withdrawSP amt => withdrawSPGuard state amt
  | .liquidateA => liquidateAGuard state

def pythonTraceEnabledFrom (state : SimplexBorrowState) :
    List BorrowCoreV0Action → Prop
  | [] => True
  | action :: rest =>
      pythonActionEnabled state action ∧
        pythonTraceEnabledFrom (stepAction state action) rest

def pythonReachableFromInit (state : SimplexBorrowState) : Prop :=
  ∃ trace,
    pythonTraceEnabledFrom borrowCoreV0InitState trace ∧
      runTrace borrowCoreV0InitState trace = state

theorem borrowCoreV0InitState_bounds :
    borrowCoreV0StateBounds borrowCoreV0InitState := by
  dsimp [borrowCoreV0StateBounds, borrowCoreV0InitState, borrowCoreV0MaxColl,
    borrowCoreV0MaxSpColl]
  norm_num [borrowCoreV0Params]

theorem borrowCoreV0StateBounds_implies_nonneg
    (state : SimplexBorrowState)
    (hBounds : borrowCoreV0StateBounds state) :
    borrowCoreV0StateNonneg state := by
  rcases hBounds with
    ⟨hAcoll0, _, hAdebt0, _, hBcoll0, _, hBdebt0, _, hFree0, _, hSpDebt0, _, hSpColl0, _⟩
  exact ⟨hAcoll0, hAdebt0, hBcoll0, hBdebt0, hFree0, hSpDebt0, hSpColl0⟩

theorem pythonActionEnabled_implies_actionEnabled
    (state : SimplexBorrowState)
    (action : BorrowCoreV0Action)
    (hEnabled : pythonActionEnabled state action) :
    actionEnabled state action := by
  cases action <;> dsimp [pythonActionEnabled, actionEnabled] at hEnabled ⊢
  · exact hEnabled.2.2
  · exact hEnabled.2.2
  · exact hEnabled
  · exact hEnabled
  · exact hEnabled
  · exact hEnabled
  · exact hEnabled
  · exact hEnabled

theorem openA_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.openA collIn debtOut)) :
    borrowCoreV0StateBounds (stepAction state (.openA collIn debtOut)) := by
  rcases hBounds with
    ⟨_, _, _, _, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      hFree0, _, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨hCollMin, hCollMax, hGuard⟩
  rcases hGuard with ⟨_, _, hMinDebt, hFreeLe, hDebtLe, _⟩
  have hDebtOut0 : 0 ≤ debtOut := by
    norm_num [borrowCoreV0Params] at hMinDebt
    linarith
  dsimp [stepAction, openA, borrowCoreV0StateBounds]
  refine ⟨?_, hCollMax, hDebtOut0, hDebtLe, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
    ?_, hFreeLe, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  · linarith
  · linarith

theorem openB_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (collIn debtOut : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.openB collIn debtOut)) :
    borrowCoreV0StateBounds (stepAction state (.openB collIn debtOut)) := by
  rcases hBounds with
    ⟨hAcoll0, hAcollMax, hAdebt0, hAdebtMax, _, _, _, _,
      hFree0, _, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨hCollMin, hCollMax, hGuard⟩
  rcases hGuard with ⟨_, _, hMinDebt, hFreeLe, hDebtLe, _⟩
  have hDebtOut0 : 0 ≤ debtOut := by
    norm_num [borrowCoreV0Params] at hMinDebt
    linarith
  dsimp [stepAction, openB, borrowCoreV0StateBounds]
  refine ⟨hAcoll0, hAcollMax, hAdebt0, hAdebtMax, ?_, hCollMax, hDebtOut0, hDebtLe,
    ?_, hFreeLe, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  · linarith
  · linarith

theorem borrowMoreA_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (extraDebt : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.borrowMoreA extraDebt)) :
    borrowCoreV0StateBounds (stepAction state (.borrowMoreA extraDebt)) := by
  rcases hBounds with
    ⟨hAcoll0, hAcollMax, _, _, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      hFree0, _, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨_, hExtra0, hFreeLe, hDebtLe, _⟩
  dsimp [stepAction, borrowMoreA, borrowCoreV0StateBounds]
  refine ⟨hAcoll0, hAcollMax, ?_, hDebtLe, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
    ?_, hFreeLe, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  · linarith
  · linarith

theorem repayA_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (amt : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.repayA amt)) :
    borrowCoreV0StateBounds (stepAction state (.repayA amt)) := by
  rcases hBounds with
    ⟨hAcoll0, hAcollMax, _, hAdebtMax, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      _, hFreeMax, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨hAmt0, hAmtDebt, hAmtFree⟩
  dsimp [stepAction, repayA, borrowCoreV0StateBounds]
  refine ⟨hAcoll0, hAcollMax, ?_, ?_, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
    ?_, ?_, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  · exact sub_nonneg.mpr hAmtDebt
  · linarith
  · exact sub_nonneg.mpr hAmtFree
  · linarith

theorem withdrawCollA_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (amt : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.withdrawCollA amt)) :
    borrowCoreV0StateBounds (stepAction state (.withdrawCollA amt)) := by
  rcases hBounds with
    ⟨_, hAcollMax, hAdebt0, hAdebtMax, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      hFree0, hFreeMax, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨_, hAmtColl, _⟩
  dsimp [stepAction, withdrawCollA, borrowCoreV0StateBounds]
  refine ⟨sub_nonneg.mpr hAmtColl, ?_, hAdebt0, hAdebtMax, hBcoll0, hBcollMax, hBdebt0,
    hBdebtMax, hFree0, hFreeMax, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  linarith

theorem depositSP_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (amt : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.depositSP amt)) :
    borrowCoreV0StateBounds (stepAction state (.depositSP amt)) := by
  rcases hBounds with
    ⟨hAcoll0, hAcollMax, hAdebt0, hAdebtMax, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      _, hFreeMax, hSpDebt0, _, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨hAmt0, hAmtFree, hSpDebtLe⟩
  dsimp [stepAction, depositSP, borrowCoreV0StateBounds]
  refine ⟨hAcoll0, hAcollMax, hAdebt0, hAdebtMax, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
    sub_nonneg.mpr hAmtFree, ?_, ?_, hSpDebtLe, hSpColl0, hSpCollMax⟩
  · linarith
  · linarith

theorem withdrawSP_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (amt : Rat)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state (.withdrawSP amt)) :
    borrowCoreV0StateBounds (stepAction state (.withdrawSP amt)) := by
  rcases hBounds with
    ⟨hAcoll0, hAcollMax, hAdebt0, hAdebtMax, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      hFree0, _, hSpDebt0, hSpDebtMax, hSpColl0, hSpCollMax⟩
  rcases hEnabled with ⟨hAmt0, hAmtSp, hFreeLe, _, _⟩
  dsimp [stepAction, withdrawSP, borrowCoreV0StateBounds]
  refine ⟨hAcoll0, hAcollMax, hAdebt0, hAdebtMax, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
    ?_, hFreeLe, sub_nonneg.mpr hAmtSp, ?_, hSpColl0, hSpCollMax⟩
  · linarith
  · linarith

theorem liquidateA_preserves_bounds_of_pythonEnabled
    (state : SimplexBorrowState)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state .liquidateA) :
    borrowCoreV0StateBounds (stepAction state .liquidateA) := by
  rcases hBounds with
    ⟨_, _, _, _, hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
      hFree0, hFreeMax, hSpDebt0, hSpDebtMax, hSpColl0, _⟩
  rcases hEnabled with ⟨_, _, hDebtSp, hSpCollLe⟩
  dsimp [stepAction, liquidateA, borrowCoreV0StateBounds]
  refine ⟨by norm_num, by norm_num [borrowCoreV0MaxColl], by norm_num,
    by norm_num [borrowCoreV0Params], hBcoll0, hBcollMax, hBdebt0, hBdebtMax,
    hFree0, hFreeMax, sub_nonneg.mpr hDebtSp, ?_, ?_, hSpCollLe⟩
  · linarith
  · linarith [hSpColl0]

theorem pythonActionEnabled_preserves_bounds
    (state : SimplexBorrowState)
    (action : BorrowCoreV0Action)
    (hBounds : borrowCoreV0StateBounds state)
    (hEnabled : pythonActionEnabled state action) :
    borrowCoreV0StateBounds (stepAction state action) := by
  cases action with
  | openA collIn debtOut =>
      exact openA_preserves_bounds_of_pythonEnabled state collIn debtOut hBounds hEnabled
  | openB collIn debtOut =>
      exact openB_preserves_bounds_of_pythonEnabled state collIn debtOut hBounds hEnabled
  | borrowMoreA extraDebt =>
      exact borrowMoreA_preserves_bounds_of_pythonEnabled state extraDebt hBounds hEnabled
  | repayA amt =>
      exact repayA_preserves_bounds_of_pythonEnabled state amt hBounds hEnabled
  | withdrawCollA amt =>
      exact withdrawCollA_preserves_bounds_of_pythonEnabled state amt hBounds hEnabled
  | depositSP amt =>
      exact depositSP_preserves_bounds_of_pythonEnabled state amt hBounds hEnabled
  | withdrawSP amt =>
      exact withdrawSP_preserves_bounds_of_pythonEnabled state amt hBounds hEnabled
  | liquidateA =>
      exact liquidateA_preserves_bounds_of_pythonEnabled state hBounds hEnabled

theorem pythonTraceEnabledFrom_implies_traceEnabledFrom
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom state trace) :
    traceEnabledFrom state trace := by
  induction trace generalizing state with
  | nil =>
      simp [traceEnabledFrom]
  | cons action rest ih =>
      rcases hTrace with ⟨hEnabled, hRest⟩
      refine ⟨pythonActionEnabled_implies_actionEnabled state action hEnabled, ?_⟩
      exact ih (state := stepAction state action) hRest

theorem pythonTraceEnabledFrom_preserves_bounds
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hBounds : borrowCoreV0StateBounds state)
    (hTrace : pythonTraceEnabledFrom state trace) :
    borrowCoreV0StateBounds (runTrace state trace) := by
  induction trace generalizing state with
  | nil =>
      simpa [runTrace, pythonTraceEnabledFrom] using hBounds
  | cons action rest ih =>
      rcases hTrace with ⟨hEnabled, hRest⟩
      have hBounds' : borrowCoreV0StateBounds (stepAction state action) := by
        exact pythonActionEnabled_preserves_bounds state action hBounds hEnabled
      simpa [runTrace, pythonTraceEnabledFrom] using
        ih (state := stepAction state action) hBounds' hRest

theorem pythonInitTrace_preserves_bounds
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    borrowCoreV0StateBounds (runTrace borrowCoreV0InitState trace) := by
  exact pythonTraceEnabledFrom_preserves_bounds
    borrowCoreV0InitState
    trace
    borrowCoreV0InitState_bounds
    hTrace

theorem pythonInitTrace_preserves_quotedInvariantState
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    quotedInvariantState (runTrace borrowCoreV0InitState trace) := by
  exact initTrace_preserves_quotedInvariantState trace
    (pythonTraceEnabledFrom_implies_traceEnabledFrom
      borrowCoreV0InitState trace hTrace)

theorem pythonInitTrace_preserves_systemNoBadDebt_at_quoted
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    systemNoBadDebt (runTrace borrowCoreV0InitState trace) borrowCoreV0Params.priceCents := by
  exact initTrace_preserves_systemNoBadDebt_at_quoted trace
    (pythonTraceEnabledFrom_implies_traceEnabledFrom
      borrowCoreV0InitState trace hTrace)

theorem pythonReachableFromInit_implies_bounds
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    borrowCoreV0StateBounds state := by
  rcases hReach with ⟨trace, hTrace, hEq⟩
  rw [← hEq]
  exact pythonInitTrace_preserves_bounds trace hTrace

theorem pythonReachableFromInit_implies_quotedInvariantState
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    quotedInvariantState state := by
  rcases hReach with ⟨trace, hTrace, hEq⟩
  rw [← hEq]
  exact pythonInitTrace_preserves_quotedInvariantState trace hTrace

theorem pythonReachableFromInit_implies_systemNoBadDebt_at_quoted
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    systemNoBadDebt state borrowCoreV0Params.priceCents := by
  rcases hReach with ⟨trace, hTrace, hEq⟩
  rw [← hEq]
  exact pythonInitTrace_preserves_systemNoBadDebt_at_quoted trace hTrace

end LeanMathlib
