import Mathlib
import LeanMathlib.DeFi.SimplexBorrowTraceDataset

namespace LeanMathlib

/-- Action index matching `ACTION_NAMES.index(cmd.tag)` in the local trace collector. -/
def collectorActionId : BorrowCoreV0Action → Nat
  | .openA _ _ => 0
  | .openB _ _ => 1
  | .borrowMoreA _ => 2
  | .repayA _ => 3
  | .withdrawCollA _ => 4
  | .depositSP _ => 5
  | .withdrawSP _ => 6
  | .liquidateA => 7

/-- Pre-state row stream matching `pre_list.append(state_to_vector(s))`. -/
def collectorPreRows
    (state : SimplexBorrowState) :
    List BorrowCoreV0Action → List (List Rat)
  | [] => []
  | action :: rest => traceStateRow state :: collectorPreRows (stepAction state action) rest

/-- Post-state row stream matching `post_list.append(state_to_vector(result.state))`. -/
def collectorPostRows
    (state : SimplexBorrowState) :
    List BorrowCoreV0Action → List (List Rat)
  | [] => []
  | action :: rest =>
      traceStateRow (stepAction state action) :: collectorPostRows (stepAction state action) rest

/-- Action-id stream matching `action_list.append(ACTION_NAMES.index(cmd.tag))`. -/
def collectorActionIds : List BorrowCoreV0Action → List Nat
  | [] => []
  | action :: rest => collectorActionId action :: collectorActionIds rest

theorem collectorActionId_lt_actionNames_length
    (action : BorrowCoreV0Action) :
    collectorActionId action < traceArtifactActionNames.length := by
  cases action <;> simp [collectorActionId, traceArtifactActionNames]

theorem traceArtifactActionName_at_collectorActionId
    (action : BorrowCoreV0Action) :
    traceArtifactActionNames[collectorActionId action]? = some (actionTag action) := by
  cases action <;> rfl

theorem collectorPreRows_length
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action) :
    (collectorPreRows state trace).length = trace.length := by
  induction trace generalizing state with
  | nil =>
      simp [collectorPreRows]
  | cons action rest ih =>
      simp [collectorPreRows, ih (state := stepAction state action)]

theorem collectorPostRows_length
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action) :
    (collectorPostRows state trace).length = trace.length := by
  induction trace generalizing state with
  | nil =>
      simp [collectorPostRows]
  | cons action rest ih =>
      simp [collectorPostRows, ih (state := stepAction state action)]

theorem collectorActionIds_length
    (trace : List BorrowCoreV0Action) :
    (collectorActionIds trace).length = trace.length := by
  induction trace with
  | nil =>
      simp [collectorActionIds]
  | cons action rest ih =>
      simp [collectorActionIds, ih]

theorem collectorActionIds_eq_map_collectorActionId
    (trace : List BorrowCoreV0Action) :
    collectorActionIds trace = trace.map collectorActionId := by
  induction trace with
  | nil =>
      simp [collectorActionIds]
  | cons action rest ih =>
      simp [collectorActionIds, ih]

theorem collectorArrays_length_agree
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action) :
    (collectorPreRows state trace).length = (collectorPostRows state trace).length ∧
      (collectorPostRows state trace).length = (collectorActionIds trace).length := by
  constructor
  · rw [collectorPreRows_length, collectorPostRows_length]
  · rw [collectorPostRows_length, collectorActionIds_length]

theorem collectorPreRows_append_terminalRow
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action) :
    collectorPreRows state trace ++ [traceStateRow (runTrace state trace)] =
      traceRowSequence state trace := by
  induction trace generalizing state with
  | nil =>
      simp [collectorPreRows, runTrace, traceRowSequence]
  | cons action rest ih =>
      simp [collectorPreRows, runTrace, traceRowSequence, ih (state := stepAction state action)]

theorem collectorPreRows_mem_traceRowSequence
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action) :
    ∀ {row}, row ∈ collectorPreRows state trace → row ∈ traceRowSequence state trace := by
  induction trace generalizing state with
  | nil =>
      intro row hRow
      simp [collectorPreRows] at hRow
  | cons action rest ih =>
      intro row hRow
      have hRow' :
          row = traceStateRow state ∨
            row ∈ collectorPreRows (stepAction state action) rest := by
        simpa [collectorPreRows] using hRow
      rcases hRow' with rfl | hTail
      · simp [traceRowSequence]
      · have hMem :
            row ∈ traceRowSequence (stepAction state action) rest := by
          exact ih (state := stepAction state action) (row := row) hTail
        simp [traceRowSequence, hMem]

theorem collectorPostRows_mem_traceRowSequence
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action) :
    ∀ {row}, row ∈ collectorPostRows state trace → row ∈ traceRowSequence state trace := by
  induction trace generalizing state with
  | nil =>
      intro row hRow
      simp [collectorPostRows] at hRow
  | cons action rest ih =>
      intro row hRow
      have hRow' :
          row = traceStateRow (stepAction state action) ∨
            row ∈ collectorPostRows (stepAction state action) rest := by
        simpa [collectorPostRows] using hRow
      rcases hRow' with rfl | hTail
      · have hHead :
            traceStateRow (stepAction state action) ∈
              traceRowSequence (stepAction state action) rest := by
          cases rest with
          | nil =>
              simp [traceRowSequence]
          | cons next rest' =>
              exact collectorPreRows_mem_traceRowSequence
                (state := stepAction state action)
                (trace := next :: rest')
                (row := traceStateRow (stepAction state action))
                (by simp [collectorPreRows])
        simp [traceRowSequence, hHead]
      · have hMem :
            row ∈ traceRowSequence (stepAction state action) rest := by
          exact ih (state := stepAction state action) (row := row) hTail
        simp [traceRowSequence, hMem]

theorem pythonTraceEnabledFrom_collectorPreRows_wellFormed
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hBounds : borrowCoreV0StateBounds state)
    (hInv : quotedInvariantState state)
    (hTrace : pythonTraceEnabledFrom state trace) :
    ∀ {row}, row ∈ collectorPreRows state trace →
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  intro row hRow
  exact pythonTraceEnabledFrom_rowsSatisfyInvariantVocabulary
    state
    trace
    hBounds
    hInv
    hTrace
    row
    (collectorPreRows_mem_traceRowSequence state trace hRow)

theorem pythonTraceEnabledFrom_collectorPostRows_wellFormed
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hBounds : borrowCoreV0StateBounds state)
    (hInv : quotedInvariantState state)
    (hTrace : pythonTraceEnabledFrom state trace) :
    ∀ {row}, row ∈ collectorPostRows state trace →
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  intro row hRow
  exact pythonTraceEnabledFrom_rowsSatisfyInvariantVocabulary
    state
    trace
    hBounds
    hInv
    hTrace
    row
    (collectorPostRows_mem_traceRowSequence state trace hRow)

theorem pythonInitTrace_collectorPreRows_wellFormed
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ {row}, row ∈ collectorPreRows borrowCoreV0InitState trace →
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  exact pythonTraceEnabledFrom_collectorPreRows_wellFormed
    borrowCoreV0InitState
    trace
    borrowCoreV0InitState_bounds
    borrowCoreV0InitState_quotedInvariantState
    hTrace

theorem pythonInitTrace_collectorPostRows_wellFormed
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ {row}, row ∈ collectorPostRows borrowCoreV0InitState trace →
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  exact pythonTraceEnabledFrom_collectorPostRows_wellFormed
    borrowCoreV0InitState
    trace
    borrowCoreV0InitState_bounds
    borrowCoreV0InitState_quotedInvariantState
    hTrace

theorem collectorActionIds_valid
    (trace : List BorrowCoreV0Action) :
    ∀ {id}, id ∈ collectorActionIds trace → id < traceArtifactActionNames.length := by
  induction trace with
  | nil =>
      intro id hId
      simp [collectorActionIds] at hId
  | cons action rest ih =>
      intro id hId
      have hId' : id = collectorActionId action ∨ id ∈ collectorActionIds rest := by
        simpa [collectorActionIds] using hId
      rcases hId' with rfl | hTail
      · exact collectorActionId_lt_actionNames_length action
      · exact ih (id := id) hTail

end LeanMathlib
