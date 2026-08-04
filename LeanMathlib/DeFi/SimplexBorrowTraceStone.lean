import LeanMathlib.DeFi.SimplexBorrowModalStone
import LeanMathlib.DeFi.SimplexBorrowTraceCollector

namespace LeanMathlib

theorem runTrace_append
    (state : SimplexBorrowState)
    (trace₁ trace₂ : List BorrowCoreV0Action) :
    runTrace state (trace₁ ++ trace₂) = runTrace (runTrace state trace₁) trace₂ := by
  induction trace₁ generalizing state with
  | nil =>
      simp [runTrace]
  | cons action rest ih =>
      simp [runTrace, ih (state := stepAction state action)]

theorem pythonTraceEnabledFrom_append
    (state : SimplexBorrowState)
    (trace₁ trace₂ : List BorrowCoreV0Action)
    (h₁ : pythonTraceEnabledFrom state trace₁)
    (h₂ : pythonTraceEnabledFrom (runTrace state trace₁) trace₂) :
    pythonTraceEnabledFrom state (trace₁ ++ trace₂) := by
  induction trace₁ generalizing state with
  | nil =>
      simpa [pythonTraceEnabledFrom, runTrace] using h₂
  | cons action rest ih =>
      rcases h₁ with ⟨hEnabled, hRest⟩
      simpa [pythonTraceEnabledFrom, runTrace] using
        And.intro hEnabled (ih (state := stepAction state action) hRest h₂)

theorem pythonReachableFromInit_step
    {state : SimplexBorrowState}
    {action : BorrowCoreV0Action}
    (hReach : pythonReachableFromInit state)
    (hEnabled : pythonActionEnabled state action) :
    pythonReachableFromInit (stepAction state action) := by
  rcases hReach with ⟨trace, hTrace, hRun⟩
  refine ⟨trace ++ [action], ?_, ?_⟩
  · have hTail : pythonTraceEnabledFrom (runTrace borrowCoreV0InitState trace) [action] := by
      rw [hRun]
      have hSingle : pythonActionEnabled state action ∧ True := ⟨hEnabled, trivial⟩
      simpa [pythonTraceEnabledFrom] using hSingle
    exact pythonTraceEnabledFrom_append borrowCoreV0InitState trace [action] hTrace hTail
  · rw [runTrace_append, hRun]
    simp [runTrace]

/-- Row-level projection into the `SimplexBorrow` modal/Stone safety clopen. -/
def rowProjectsToSimplexBorrowSafetyClopen (row : List Rat) : Prop :=
  ∃ state : SimplexBorrowState,
    pythonReachableFromInit state ∧
      row = traceStateRow state ∧
        Stone.principalPoint
            (Relational.theoryQuotientMk
              simplexBorrowStepRel simplexBorrowValuation state) ∈
          simplexBorrowSafetyClopen

theorem rowProjectsToSimplexBorrowSafetyClopen_traceStateRow
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    rowProjectsToSimplexBorrowSafetyClopen (traceStateRow state) := by
  refine ⟨state, hReach, rfl, ?_⟩
  exact pythonReachableFromInit_mem_simplexBorrowSafetyClopen hReach

theorem rowProjectsToSimplexBorrowSafetyClopen_implies_rowWellTyped
    {row : List Rat}
    (hProj : rowProjectsToSimplexBorrowSafetyClopen row) :
    rowWellTyped row := by
  rcases hProj with ⟨state, hReach, hRow, _hClopen⟩
  rw [hRow]
  exact pythonReachableFromInit_implies_rowWellTyped hReach

theorem rowProjectsToSimplexBorrowSafetyClopen_implies_rowSatisfiesInvariantVocabulary
    {row : List Rat}
    (hProj : rowProjectsToSimplexBorrowSafetyClopen row) :
    rowSatisfiesInvariantVocabulary row := by
  rcases hProj with ⟨state, hReach, hRow, _hClopen⟩
  rw [hRow]
  exact bounds_and_quotedInvariant_imply_rowSatisfiesInvariantVocabulary
    state
    (pythonReachableFromInit_implies_bounds hReach)
    (pythonReachableFromInit_implies_quotedInvariantState hReach)

theorem pythonTraceEnabledFrom_traceRows_projectToSimplexBorrowSafetyClopen
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hReach : pythonReachableFromInit state)
    (hTrace : pythonTraceEnabledFrom state trace) :
    ∀ row ∈ traceRowSequence state trace,
      rowProjectsToSimplexBorrowSafetyClopen row := by
  induction trace generalizing state with
  | nil =>
      intro row hRow
      have hEq : row = traceStateRow state := by
        simpa [traceRowSequence] using hRow
      rw [hEq]
      exact rowProjectsToSimplexBorrowSafetyClopen_traceStateRow hReach
  | cons action rest ih =>
      rcases hTrace with ⟨hEnabled, hRest⟩
      intro row hRow
      have hCases :
          row = traceStateRow state ∨
            row ∈ traceRowSequence (stepAction state action) rest := by
        simpa [traceRowSequence] using hRow
      rcases hCases with rfl | hTail
      · exact rowProjectsToSimplexBorrowSafetyClopen_traceStateRow hReach
      · have hReach' : pythonReachableFromInit (stepAction state action) := by
          exact pythonReachableFromInit_step hReach hEnabled
        exact ih (state := stepAction state action) hReach' hRest row hTail

theorem pythonInitTrace_traceRows_projectToSimplexBorrowSafetyClopen
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ row ∈ traceRowSequence borrowCoreV0InitState trace,
      rowProjectsToSimplexBorrowSafetyClopen row := by
  have hReachInit : pythonReachableFromInit borrowCoreV0InitState := by
    refine ⟨[], ?_, ?_⟩
    · simp [pythonTraceEnabledFrom]
    · simp [runTrace, borrowCoreV0InitState]
  exact pythonTraceEnabledFrom_traceRows_projectToSimplexBorrowSafetyClopen
    borrowCoreV0InitState trace hReachInit hTrace

theorem pythonInitTrace_collectorPreRows_projectToSimplexBorrowSafetyClopen
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ {row}, row ∈ collectorPreRows borrowCoreV0InitState trace →
      rowProjectsToSimplexBorrowSafetyClopen row := by
  intro row hRow
  exact pythonInitTrace_traceRows_projectToSimplexBorrowSafetyClopen
    trace hTrace row
    (collectorPreRows_mem_traceRowSequence borrowCoreV0InitState trace hRow)

theorem pythonInitTrace_collectorPostRows_projectToSimplexBorrowSafetyClopen
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ {row}, row ∈ collectorPostRows borrowCoreV0InitState trace →
      rowProjectsToSimplexBorrowSafetyClopen row := by
  intro row hRow
  exact pythonInitTrace_traceRows_projectToSimplexBorrowSafetyClopen
    trace hTrace row
    (collectorPostRows_mem_traceRowSequence borrowCoreV0InitState trace hRow)

theorem pythonInitTrace_collectorPreRows_safeAndWellFormed
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ {row}, row ∈ collectorPreRows borrowCoreV0InitState trace →
      rowProjectsToSimplexBorrowSafetyClopen row ∧
        rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  intro row hRow
  have hProj :
      rowProjectsToSimplexBorrowSafetyClopen row := by
    exact pythonInitTrace_collectorPreRows_projectToSimplexBorrowSafetyClopen trace hTrace hRow
  exact ⟨hProj,
    rowProjectsToSimplexBorrowSafetyClopen_implies_rowWellTyped hProj,
    rowProjectsToSimplexBorrowSafetyClopen_implies_rowSatisfiesInvariantVocabulary hProj⟩

theorem pythonInitTrace_collectorPostRows_safeAndWellFormed
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ {row}, row ∈ collectorPostRows borrowCoreV0InitState trace →
      rowProjectsToSimplexBorrowSafetyClopen row ∧
        rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  intro row hRow
  have hProj :
      rowProjectsToSimplexBorrowSafetyClopen row := by
    exact pythonInitTrace_collectorPostRows_projectToSimplexBorrowSafetyClopen trace hTrace hRow
  exact ⟨hProj,
    rowProjectsToSimplexBorrowSafetyClopen_implies_rowWellTyped hProj,
    rowProjectsToSimplexBorrowSafetyClopen_implies_rowSatisfiesInvariantVocabulary hProj⟩

end LeanMathlib
