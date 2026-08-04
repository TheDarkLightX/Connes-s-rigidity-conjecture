import Mathlib
import LeanMathlib.DeFi.SimplexBorrowYamlBridge

namespace LeanMathlib

/--
State-key order matching both the local trace collector `STATE_KEYS` and the
Morph domain `_STATE_KEYS`.
-/
def traceArtifactStateKeys : List String :=
  ["price_cents", "coll_a", "debt_a", "coll_b", "debt_b", "free_debt", "sp_debt", "sp_coll"]

/--
Action-name order matching both the local trace collector `ACTION_NAMES` and
the Python kernel's action handler surface.
-/
def traceArtifactActionNames : List String :=
  ["open_a", "open_b", "borrow_more_a", "repay_a", "withdraw_coll_a",
    "deposit_sp", "withdraw_sp", "liquidate_a"]

/-- Encode a Lean state into the ordered row format used by the trace artifacts. -/
def traceStateRow (state : SimplexBorrowState) : List Rat :=
  let obs := encodeState state
  [obs.priceCents, obs.collA, obs.debtA, obs.collB, obs.debtB,
    obs.freeDebt, obs.spDebt, obs.spColl]

/-- Decode a row-format trace state back into the observable encoded state. -/
def decodeTraceStateRow : List Rat → Option BorrowCoreV0EncodedState
  | [priceCents, collA, debtA, collB, debtB, freeDebt, spDebt, spColl] =>
      some
        { priceCents := priceCents
          collA := collA
          debtA := debtA
          collB := collB
          debtB := debtB
          freeDebt := freeDebt
          spDebt := spDebt
          spColl := spColl }
  | _ => none

/-- Row-level typedness predicate for a trace-artifact state row. -/
def rowWellTyped (row : List Rat) : Prop :=
  ∃ obs, decodeTraceStateRow row = some obs ∧ encodedStateWithinYamlTypes obs

/-- Row-level named invariant predicate for a trace-artifact state row. -/
def rowInvariant (inv : BorrowCoreV0InvariantId) (row : List Rat) : Prop :=
  ∃ obs, decodeTraceStateRow row = some obs ∧ encodedInvariant inv obs

theorem traceArtifactStateKeys_match_collect_and_morph :
    traceArtifactStateKeys = yamlObservableFieldNames := by
  rfl

theorem traceArtifactActionNames_match_collect :
    traceArtifactActionNames = yamlActionTags := by
  rfl

theorem traceStateRow_length
    (state : SimplexBorrowState) :
    (traceStateRow state).length = 8 := by
  simp [traceStateRow]

theorem decodeTraceStateRow_traceStateRow
    (state : SimplexBorrowState) :
    decodeTraceStateRow (traceStateRow state) = some (encodeState state) := by
  rfl

theorem traceStateRow_borrowCoreV0InitState :
    traceStateRow borrowCoreV0InitState = [100, 0, 0, 0, 0, 0, 0, 0] := by
  norm_num [traceStateRow, encodeState, borrowCoreV0InitState, borrowCoreV0Params]

theorem rowWellTyped_traceStateRow_iff
    (state : SimplexBorrowState) :
    rowWellTyped (traceStateRow state) ↔
      encodedStateWithinYamlTypes (encodeState state) := by
  constructor
  · intro h
    rcases h with ⟨obs, hDecode, hTyped⟩
    have hSome : some obs = some (encodeState state) := by
      rw [← hDecode, decodeTraceStateRow_traceStateRow]
    injection hSome with hObs
    simpa [hObs] using hTyped
  · intro hTyped
    exact ⟨encodeState state, decodeTraceStateRow_traceStateRow state, hTyped⟩

theorem rowInvariant_traceStateRow_iff
    (state : SimplexBorrowState)
    (inv : BorrowCoreV0InvariantId) :
    rowInvariant inv (traceStateRow state) ↔
      encodedInvariant inv (encodeState state) := by
  constructor
  · intro h
    rcases h with ⟨obs, hDecode, hInv⟩
    have hSome : some obs = some (encodeState state) := by
      rw [← hDecode, decodeTraceStateRow_traceStateRow]
    injection hSome with hObs
    simpa [hObs] using hInv
  · intro hInv
    exact ⟨encodeState state, decodeTraceStateRow_traceStateRow state, hInv⟩

theorem pythonReachableFromInit_implies_rowWellTyped
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    rowWellTyped (traceStateRow state) := by
  exact (rowWellTyped_traceStateRow_iff state).2
    (pythonReachableFromInit_implies_encodedStateWithinYamlTypes hReach)

theorem pythonReachableFromInit_implies_rowInvariant
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    ∀ inv ∈ yamlInvariantIds, rowInvariant inv (traceStateRow state) := by
  intro inv hMem
  exact (rowInvariant_traceStateRow_iff state inv).2
    (allEncodedInvariantsHold_of_pythonReachable hReach inv hMem)

end LeanMathlib
