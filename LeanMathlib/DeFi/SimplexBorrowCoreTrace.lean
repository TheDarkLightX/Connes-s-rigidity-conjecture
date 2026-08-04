import Mathlib
import LeanMathlib.DeFi.SimplexBorrowCoreStep

namespace LeanMathlib

/-- Canonical zeroed state matching the local `borrow_core_v0.py` `init_state()`. -/
def borrowCoreV0InitState : SimplexBorrowState :=
  { troveA := { collateral := 0, debt := 0 }
    troveB := { collateral := 0, debt := 0 }
    freeDebt := 0
    spDebt := 0
    spColl := 0 }

/-- Execute a list of arithmetic `borrow_core_v0` actions. -/
def runTrace (state : SimplexBorrowState) : List BorrowCoreV0Action → SimplexBorrowState
  | [] => state
  | action :: rest => runTrace (stepAction state action) rest

/-- All actions in the trace are enabled when executed from left to right. -/
def traceEnabledFrom (state : SimplexBorrowState) : List BorrowCoreV0Action → Prop
  | [] => True
  | action :: rest => actionEnabled state action ∧ traceEnabledFrom (stepAction state action) rest

/-- Reachability from the canonical init state via an enabled action trace. -/
def reachableFromInit (state : SimplexBorrowState) : Prop :=
  ∃ trace,
    traceEnabledFrom borrowCoreV0InitState trace ∧
      runTrace borrowCoreV0InitState trace = state

theorem borrowCoreV0InitState_quotedInvariantState :
    quotedInvariantState borrowCoreV0InitState := by
  dsimp [quotedInvariantState, borrowCoreV0InitState, supplyConservation, troveNoBadDebt]
  norm_num [borrowCoreV0Params]

theorem borrowCoreV0InitState_systemNoBadDebt_at_quoted :
    systemNoBadDebt borrowCoreV0InitState borrowCoreV0Params.priceCents := by
  exact quotedInvariantState_implies_systemNoBadDebt
    borrowCoreV0InitState
    borrowCoreV0InitState_quotedInvariantState

theorem traceEnabledFrom_preserves_quotedInvariantState
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hInv : quotedInvariantState state)
    (hTrace : traceEnabledFrom state trace) :
    quotedInvariantState (runTrace state trace) := by
  induction trace generalizing state with
  | nil =>
      simpa [runTrace, traceEnabledFrom] using hInv
  | cons action rest ih =>
      rcases hTrace with ⟨hEnabled, hRest⟩
      have hInv' : quotedInvariantState (stepAction state action) := by
        exact actionEnabled_preserves_quotedInvariantState state action hInv hEnabled
      simpa [runTrace, traceEnabledFrom] using
        ih (state := stepAction state action) hInv' hRest

theorem traceEnabledFrom_preserves_systemNoBadDebt_at_quoted
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hInv : quotedInvariantState state)
    (hTrace : traceEnabledFrom state trace) :
    systemNoBadDebt (runTrace state trace) borrowCoreV0Params.priceCents := by
  exact quotedInvariantState_implies_systemNoBadDebt
    (runTrace state trace)
    (traceEnabledFrom_preserves_quotedInvariantState state trace hInv hTrace)

theorem initTrace_preserves_quotedInvariantState
    (trace : List BorrowCoreV0Action)
    (hTrace : traceEnabledFrom borrowCoreV0InitState trace) :
    quotedInvariantState (runTrace borrowCoreV0InitState trace) := by
  exact traceEnabledFrom_preserves_quotedInvariantState
    borrowCoreV0InitState
    trace
    borrowCoreV0InitState_quotedInvariantState
    hTrace

theorem initTrace_preserves_systemNoBadDebt_at_quoted
    (trace : List BorrowCoreV0Action)
    (hTrace : traceEnabledFrom borrowCoreV0InitState trace) :
    systemNoBadDebt (runTrace borrowCoreV0InitState trace) borrowCoreV0Params.priceCents := by
  exact traceEnabledFrom_preserves_systemNoBadDebt_at_quoted
    borrowCoreV0InitState
    trace
    borrowCoreV0InitState_quotedInvariantState
    hTrace

theorem reachableFromInit_implies_quotedInvariantState
    {state : SimplexBorrowState}
    (hReach : reachableFromInit state) :
    quotedInvariantState state := by
  rcases hReach with ⟨trace, hTrace, hEq⟩
  rw [← hEq]
  exact initTrace_preserves_quotedInvariantState trace hTrace

theorem reachableFromInit_implies_systemNoBadDebt_at_quoted
    {state : SimplexBorrowState}
    (hReach : reachableFromInit state) :
    systemNoBadDebt state borrowCoreV0Params.priceCents := by
  rcases hReach with ⟨trace, hTrace, hEq⟩
  rw [← hEq]
  exact initTrace_preserves_systemNoBadDebt_at_quoted trace hTrace

end LeanMathlib
