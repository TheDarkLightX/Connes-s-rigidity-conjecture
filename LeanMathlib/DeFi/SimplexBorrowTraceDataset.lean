import Mathlib
import LeanMathlib.DeFi.SimplexBorrowTraceArtifacts

namespace LeanMathlib

/-- Recursive state sequence matching the pre/post row unfolding of the local trace collector. -/
def traceStateSequence
    (state : SimplexBorrowState) :
    List BorrowCoreV0Action → List SimplexBorrowState
  | [] => [state]
  | action :: rest => state :: traceStateSequence (stepAction state action) rest

/-- Recursive row sequence induced by `traceStateSequence`. -/
def traceRowSequence (state : SimplexBorrowState) : List BorrowCoreV0Action → List (List Rat)
  | [] => [traceStateRow state]
  | action :: rest => traceStateRow state :: traceRowSequence (stepAction state action) rest

/-- All named Morph/YAML invariants hold on a given trace row. -/
def rowSatisfiesInvariantVocabulary (row : List Rat) : Prop :=
  ∀ inv ∈ yamlInvariantIds, rowInvariant inv row

def morphInvariantNames : List String :=
  ["SupplyConservation", "NoBadDebtA", "NoBadDebtB", "SystemNoBadDebt"]

theorem morphInvariantNames_match_yamlInvariantNames :
    morphInvariantNames = yamlInvariantNames := by
  rfl

theorem bounds_and_quotedInvariant_imply_rowSatisfiesInvariantVocabulary
    (state : SimplexBorrowState)
    (hBounds : borrowCoreV0StateBounds state)
    (hInv : quotedInvariantState state) :
    rowSatisfiesInvariantVocabulary (traceStateRow state) := by
  intro inv hMem
  rcases hInv with ⟨hSupply, hA, hB, hSp⟩
  have hSystem :
      systemNoBadDebt state borrowCoreV0Params.priceCents := by
    exact quotedInvariantState_implies_systemNoBadDebt state
      ⟨hSupply, hA, hB, hSp⟩
  have hCases :
      inv = .supplyConservation ∨ inv = .noBadDebtA ∨
        inv = .noBadDebtB ∨ inv = .systemNoBadDebt := by
    simpa [yamlInvariantIds] using hMem
  rcases hCases with rfl | rfl | rfl | rfl
  · exact (rowInvariant_traceStateRow_iff state .supplyConservation).2 <|
      (encodedInvariant_supplyConservation_iff state).2 hSupply
  · exact (rowInvariant_traceStateRow_iff state .noBadDebtA).2 <|
      (encodedInvariant_noBadDebtA_iff_of_bounds state hBounds).2 hA
  · exact (rowInvariant_traceStateRow_iff state .noBadDebtB).2 <|
      (encodedInvariant_noBadDebtB_iff_of_bounds state hBounds).2 hB
  · exact (rowInvariant_traceStateRow_iff state .systemNoBadDebt).2 <|
      (encodedInvariant_systemNoBadDebt_iff state).2 hSystem

theorem pythonTraceEnabledFrom_rowsSatisfyInvariantVocabulary
    (state : SimplexBorrowState)
    (trace : List BorrowCoreV0Action)
    (hBounds : borrowCoreV0StateBounds state)
    (hInv : quotedInvariantState state)
    (hTrace : pythonTraceEnabledFrom state trace) :
    ∀ row ∈ traceRowSequence state trace,
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  induction trace generalizing state with
  | nil =>
      intro row hRow
      have hRow' : row = traceStateRow state := by
        simpa [traceRowSequence] using hRow
      rcases hRow' with rfl
      refine ⟨?_, ?_⟩
      · exact (rowWellTyped_traceStateRow_iff state).2 <|
          (encodedStateWithinYamlTypes_encodeState_iff state).2 hBounds
      · exact bounds_and_quotedInvariant_imply_rowSatisfiesInvariantVocabulary state hBounds hInv
  | cons action rest ih =>
      rcases hTrace with ⟨hEnabled, hRest⟩
      intro row hRow
      have hRow' :
          row = traceStateRow state ∨
            row ∈ traceRowSequence (stepAction state action) rest := by
        simpa [traceRowSequence] using hRow
      rcases hRow' with rfl | hTail
      · refine ⟨?_, ?_⟩
        · exact (rowWellTyped_traceStateRow_iff state).2 <|
            (encodedStateWithinYamlTypes_encodeState_iff state).2 hBounds
        · exact bounds_and_quotedInvariant_imply_rowSatisfiesInvariantVocabulary state hBounds hInv
      · have hBounds' : borrowCoreV0StateBounds (stepAction state action) := by
          exact pythonActionEnabled_preserves_bounds state action hBounds hEnabled
        have hInv' : quotedInvariantState (stepAction state action) := by
          exact actionEnabled_preserves_quotedInvariantState
            state
            action
            hInv
            (pythonActionEnabled_implies_actionEnabled state action hEnabled)
        exact ih (state := stepAction state action) hBounds' hInv' hRest row hTail

theorem pythonInitTrace_rowsSatisfyInvariantVocabulary
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ row ∈ traceRowSequence borrowCoreV0InitState trace,
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
  exact pythonTraceEnabledFrom_rowsSatisfyInvariantVocabulary
    borrowCoreV0InitState
    trace
    borrowCoreV0InitState_bounds
    borrowCoreV0InitState_quotedInvariantState
    hTrace

theorem pythonInitTrace_rowsSatisfyNamedMorphInvariant
    (trace : List BorrowCoreV0Action)
    (hTrace : pythonTraceEnabledFrom borrowCoreV0InitState trace) :
    ∀ row ∈ traceRowSequence borrowCoreV0InitState trace,
      ∀ name ∈ morphInvariantNames,
        ∃ inv,
          inv ∈ yamlInvariantIds ∧
            invariantIdString inv = name ∧
              rowInvariant inv row := by
  intro row hRow name hName
  have hRowInv :
      rowWellTyped row ∧ rowSatisfiesInvariantVocabulary row := by
    exact pythonInitTrace_rowsSatisfyInvariantVocabulary trace hTrace row hRow
  have hCases :
      name = "SupplyConservation" ∨ name = "NoBadDebtA" ∨
        name = "NoBadDebtB" ∨ name = "SystemNoBadDebt" := by
    simpa [morphInvariantNames] using hName
  rcases hCases with rfl | rfl | rfl | rfl
  · exact ⟨.supplyConservation, by simp [yamlInvariantIds], rfl,
      hRowInv.2 .supplyConservation (by simp [yamlInvariantIds])⟩
  · exact ⟨.noBadDebtA, by simp [yamlInvariantIds], rfl,
      hRowInv.2 .noBadDebtA (by simp [yamlInvariantIds])⟩
  · exact ⟨.noBadDebtB, by simp [yamlInvariantIds], rfl,
      hRowInv.2 .noBadDebtB (by simp [yamlInvariantIds])⟩
  · exact ⟨.systemNoBadDebt, by simp [yamlInvariantIds], rfl,
      hRowInv.2 .systemNoBadDebt (by simp [yamlInvariantIds])⟩

end LeanMathlib
