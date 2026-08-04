import Mathlib
import LeanMathlib.DeFi.SimplexBorrowCoreBounds

namespace LeanMathlib

/-- Encoded observable state matching the ESSO `borrow_core_v0.yaml` surface. -/
structure BorrowCoreV0EncodedState where
  priceCents : Rat
  collA : Rat
  debtA : Rat
  collB : Rat
  debtB : Rat
  freeDebt : Rat
  spDebt : Rat
  spColl : Rat

/-- Observable field order matching the YAML `state_vars` / refinement surface. -/
def yamlObservableFieldNames : List String :=
  ["price_cents", "coll_a", "debt_a", "coll_b", "debt_b", "free_debt", "sp_debt", "sp_coll"]

/-- Action tags matching the YAML `actions[*].id` surface. -/
def yamlActionTags : List String :=
  ["open_a", "open_b", "borrow_more_a", "repay_a", "withdraw_coll_a",
    "deposit_sp", "withdraw_sp", "liquidate_a"]

/-- Invariant ids matching the YAML `invariants[*].id` surface. -/
inductive BorrowCoreV0InvariantId where
  | supplyConservation
  | noBadDebtA
  | noBadDebtB
  | systemNoBadDebt
deriving DecidableEq, Repr

def yamlInvariantIds : List BorrowCoreV0InvariantId :=
  [.supplyConservation, .noBadDebtA, .noBadDebtB, .systemNoBadDebt]

def invariantIdString : BorrowCoreV0InvariantId → String
  | .supplyConservation => "SupplyConservation"
  | .noBadDebtA => "NoBadDebtA"
  | .noBadDebtB => "NoBadDebtB"
  | .systemNoBadDebt => "SystemNoBadDebt"

def yamlInvariantNames : List String :=
  yamlInvariantIds.map invariantIdString

/-- Encode the Lean arithmetic state into the YAML observable surface. -/
def encodeState (state : SimplexBorrowState) : BorrowCoreV0EncodedState :=
  { priceCents := borrowCoreV0Params.priceCents
    collA := state.troveA.collateral
    debtA := state.troveA.debt
    collB := state.troveB.collateral
    debtB := state.troveB.debt
    freeDebt := state.freeDebt
    spDebt := state.spDebt
    spColl := state.spColl }

/-- Encoded state satisfies the YAML `state_vars` numeric envelope. -/
def encodedStateWithinYamlTypes (obs : BorrowCoreV0EncodedState) : Prop :=
  obs.priceCents = borrowCoreV0Params.priceCents ∧
    0 ≤ obs.collA ∧
    obs.collA ≤ borrowCoreV0MaxColl ∧
    0 ≤ obs.debtA ∧
    obs.debtA ≤ borrowCoreV0Params.maxDebt ∧
    0 ≤ obs.collB ∧
    obs.collB ≤ borrowCoreV0MaxColl ∧
    0 ≤ obs.debtB ∧
    obs.debtB ≤ borrowCoreV0Params.maxDebt ∧
    0 ≤ obs.freeDebt ∧
    obs.freeDebt ≤ borrowCoreV0Params.maxDebtSupply ∧
    0 ≤ obs.spDebt ∧
    obs.spDebt ≤ borrowCoreV0Params.maxDebtSupply ∧
    0 ≤ obs.spColl ∧
    obs.spColl ≤ borrowCoreV0MaxSpColl

/-- Evaluate a named YAML invariant on an encoded observable state. -/
def encodedInvariant (inv : BorrowCoreV0InvariantId) (obs : BorrowCoreV0EncodedState) : Prop :=
  match inv with
  | .supplyConservation =>
      obs.freeDebt + obs.spDebt = obs.debtA + obs.debtB
  | .noBadDebtA =>
      obs.debtA = 0 ∨ obs.collA * obs.priceCents ≥ obs.debtA
  | .noBadDebtB =>
      obs.debtB = 0 ∨ obs.collB * obs.priceCents ≥ obs.debtB
  | .systemNoBadDebt =>
      (obs.collA + obs.collB + obs.spColl) * obs.priceCents ≥ obs.debtA + obs.debtB

/-- YAML action tag encoding for the arithmetic Lean action surface. -/
def actionTag : BorrowCoreV0Action → String
  | .openA _ _ => "open_a"
  | .openB _ _ => "open_b"
  | .borrowMoreA _ => "borrow_more_a"
  | .repayA _ => "repay_a"
  | .withdrawCollA _ => "withdraw_coll_a"
  | .depositSP _ => "deposit_sp"
  | .withdrawSP _ => "withdraw_sp"
  | .liquidateA => "liquidate_a"

/-- YAML parameter names for each action tag. -/
def actionParamNames : BorrowCoreV0Action → List String
  | .openA _ _ => ["coll_in", "debt_out"]
  | .openB _ _ => ["coll_in", "debt_out"]
  | .borrowMoreA _ => ["extra_debt"]
  | .repayA _ => ["amt"]
  | .withdrawCollA _ => ["amt"]
  | .depositSP _ => ["amt"]
  | .withdrawSP _ => ["amt"]
  | .liquidateA => []

theorem yamlObservableFieldNames_match_yaml :
    yamlObservableFieldNames =
      ["price_cents", "coll_a", "debt_a", "coll_b",
        "debt_b", "free_debt", "sp_debt", "sp_coll"] := by
  rfl

theorem yamlInvariantNames_match_yaml :
    yamlInvariantNames =
      ["SupplyConservation", "NoBadDebtA", "NoBadDebtB", "SystemNoBadDebt"] := by
  rfl

theorem actionTag_mem_yamlActionTags
    (action : BorrowCoreV0Action) :
    actionTag action ∈ yamlActionTags := by
  cases action <;> simp [actionTag, yamlActionTags]

theorem encodeState_borrowCoreV0InitState :
    encodeState borrowCoreV0InitState =
      { priceCents := 100
        collA := 0
        debtA := 0
        collB := 0
        debtB := 0
        freeDebt := 0
        spDebt := 0
        spColl := 0 } := by
  rfl

theorem encodedStateWithinYamlTypes_encodeState_iff
    (state : SimplexBorrowState) :
    encodedStateWithinYamlTypes (encodeState state) ↔
      borrowCoreV0StateBounds state := by
  constructor
  · intro h
    dsimp [encodedStateWithinYamlTypes, encodeState, borrowCoreV0StateBounds] at h
    exact h.2
  · intro hBounds
    exact by
      dsimp [encodedStateWithinYamlTypes, encodeState, borrowCoreV0StateBounds]
      exact ⟨rfl, hBounds⟩

theorem encodedInvariant_supplyConservation_iff
    (state : SimplexBorrowState) :
    encodedInvariant .supplyConservation (encodeState state) ↔
      supplyConservation state := by
  rfl

theorem encodedInvariant_noBadDebtA_iff_of_bounds
    (state : SimplexBorrowState)
    (hBounds : borrowCoreV0StateBounds state) :
    encodedInvariant .noBadDebtA (encodeState state) ↔
      troveNoBadDebt state.troveA borrowCoreV0Params.priceCents := by
  rcases hBounds with ⟨hColl0, _, hDebt0, _, _, _, _, _, _, _, _, _, _, _⟩
  constructor
  · intro h
    rcases h with hZero | hGe
    · dsimp [troveNoBadDebt]
      have hZero' : state.troveA.debt = 0 := by
        simpa [encodeState] using hZero
      rw [hZero']
      have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
        norm_num [borrowCoreV0Params]
      have : 0 ≤ state.troveA.collateral * borrowCoreV0Params.priceCents := mul_nonneg hColl0 hPrice
      linarith
    · simpa [troveNoBadDebt, encodeState] using hGe
  · intro h
    by_cases hZero : state.troveA.debt = 0
    · exact Or.inl hZero
    · exact Or.inr (by simpa [troveNoBadDebt, encodeState] using h)

theorem encodedInvariant_noBadDebtB_iff_of_bounds
    (state : SimplexBorrowState)
    (hBounds : borrowCoreV0StateBounds state) :
    encodedInvariant .noBadDebtB (encodeState state) ↔
      troveNoBadDebt state.troveB borrowCoreV0Params.priceCents := by
  rcases hBounds with ⟨_, _, _, _, hColl0, _, hDebt0, _, _, _, _, _, _, _⟩
  constructor
  · intro h
    rcases h with hZero | hGe
    · dsimp [troveNoBadDebt]
      have hZero' : state.troveB.debt = 0 := by
        simpa [encodeState] using hZero
      rw [hZero']
      have hPrice : 0 ≤ borrowCoreV0Params.priceCents := by
        norm_num [borrowCoreV0Params]
      have : 0 ≤ state.troveB.collateral * borrowCoreV0Params.priceCents := mul_nonneg hColl0 hPrice
      linarith
    · simpa [troveNoBadDebt, encodeState] using hGe
  · intro h
    by_cases hZero : state.troveB.debt = 0
    · exact Or.inl hZero
    · exact Or.inr (by simpa [troveNoBadDebt, encodeState] using h)

theorem encodedInvariant_systemNoBadDebt_iff
    (state : SimplexBorrowState) :
    encodedInvariant .systemNoBadDebt (encodeState state) ↔
      systemNoBadDebt state borrowCoreV0Params.priceCents := by
  rfl

theorem pythonReachableFromInit_implies_encodedStateWithinYamlTypes
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    encodedStateWithinYamlTypes (encodeState state) := by
  exact (encodedStateWithinYamlTypes_encodeState_iff state).2
    (pythonReachableFromInit_implies_bounds hReach)

theorem allEncodedInvariantsHold_of_pythonReachable
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    ∀ inv ∈ yamlInvariantIds,
      encodedInvariant inv (encodeState state) := by
  intro inv hMem
  have hBounds : borrowCoreV0StateBounds state := by
    exact pythonReachableFromInit_implies_bounds hReach
  have hInv : quotedInvariantState state := by
    exact pythonReachableFromInit_implies_quotedInvariantState hReach
  rcases hInv with ⟨hSupply, hA, hB, _hSp⟩
  have hCases :
      inv = .supplyConservation ∨ inv = .noBadDebtA ∨
        inv = .noBadDebtB ∨ inv = .systemNoBadDebt := by
    simpa [yamlInvariantIds] using hMem
  rcases hCases with rfl | rfl | rfl | rfl
  · exact (encodedInvariant_supplyConservation_iff state).2 hSupply
  · exact (encodedInvariant_noBadDebtA_iff_of_bounds state hBounds).2 hA
  · exact (encodedInvariant_noBadDebtB_iff_of_bounds state hBounds).2 hB
  · exact (encodedInvariant_systemNoBadDebt_iff state).2
      (pythonReachableFromInit_implies_systemNoBadDebt_at_quoted hReach)

end LeanMathlib
