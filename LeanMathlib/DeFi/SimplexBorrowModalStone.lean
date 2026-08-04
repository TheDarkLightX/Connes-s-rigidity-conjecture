import LeanMathlib.DeFi.SimplexBorrowCoreBounds
import LeanMathlib.Order.StoneQuotientSubalgebra

namespace LeanMathlib

/-- Concrete atomic proposition surface for the local `SimplexBorrow` safety model. -/
inductive SimplexBorrowAtom
  | quotedInvariant
  | bounds
  | systemNoBadDebt
  deriving Repr, DecidableEq

/-- Concrete one-step transition relation induced by Python-enabled arithmetic actions. -/
def simplexBorrowStepRel (state next : SimplexBorrowState) : Prop :=
  ∃ action : BorrowCoreV0Action,
    pythonActionEnabled state action ∧ stepAction state action = next

/-- Valuation of the protocol-safety atomic propositions on concrete states. -/
def simplexBorrowValuation : SimplexBorrowAtom → Set SimplexBorrowState
  | .quotedInvariant => { state | quotedInvariantState state }
  | .bounds => { state | borrowCoreV0StateBounds state }
  | .systemNoBadDebt => { state | systemNoBadDebt state borrowCoreV0Params.priceCents }

@[simp] theorem mem_simplexBorrowValuation_quotedInvariant {state : SimplexBorrowState} :
    state ∈ simplexBorrowValuation .quotedInvariant ↔ quotedInvariantState state := by
  rfl

@[simp] theorem mem_simplexBorrowValuation_bounds {state : SimplexBorrowState} :
    state ∈ simplexBorrowValuation .bounds ↔ borrowCoreV0StateBounds state := by
  rfl

@[simp] theorem mem_simplexBorrowValuation_systemNoBadDebt {state : SimplexBorrowState} :
    state ∈ simplexBorrowValuation .systemNoBadDebt ↔
      systemNoBadDebt state borrowCoreV0Params.priceCents := by
  rfl

theorem simplexBorrowStepRel_successor_quotedInvariant
    {state next : SimplexBorrowState}
    (hReach : pythonReachableFromInit state)
    (hStep : simplexBorrowStepRel state next) :
    quotedInvariantState next := by
  have hInv : quotedInvariantState state := by
    exact pythonReachableFromInit_implies_quotedInvariantState hReach
  rcases hStep with ⟨action, hEnabled, rfl⟩
  exact actionEnabled_preserves_quotedInvariantState state action hInv
    (pythonActionEnabled_implies_actionEnabled state action hEnabled)

theorem simplexBorrowStepRel_successor_bounds
    {state next : SimplexBorrowState}
    (hReach : pythonReachableFromInit state)
    (hStep : simplexBorrowStepRel state next) :
    borrowCoreV0StateBounds next := by
  have hBounds : borrowCoreV0StateBounds state := pythonReachableFromInit_implies_bounds hReach
  rcases hStep with ⟨action, hEnabled, rfl⟩
  exact pythonActionEnabled_preserves_bounds state action hBounds hEnabled

theorem simplexBorrowStepRel_successor_systemNoBadDebt
    {state next : SimplexBorrowState}
    (hReach : pythonReachableFromInit state)
    (hStep : simplexBorrowStepRel state next) :
    systemNoBadDebt next borrowCoreV0Params.priceCents := by
  have hInv : quotedInvariantState state := by
    exact pythonReachableFromInit_implies_quotedInvariantState hReach
  rcases hStep with ⟨action, hEnabled, rfl⟩
  exact actionEnabled_preserves_systemNoBadDebt_at_quoted state action hInv
    (pythonActionEnabled_implies_actionEnabled state action hEnabled)

theorem pythonReachableFromInit_satisfies_atom_quotedInvariant
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    Relational.Satisfies simplexBorrowStepRel simplexBorrowValuation state
      (.atom .quotedInvariant) := by
  simpa [Relational.Satisfies, Relational.eval] using
    (pythonReachableFromInit_implies_quotedInvariantState hReach)

theorem pythonReachableFromInit_satisfies_atom_bounds
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    Relational.Satisfies simplexBorrowStepRel simplexBorrowValuation state
      (.atom .bounds) := by
  simpa [Relational.Satisfies, Relational.eval] using
    (pythonReachableFromInit_implies_bounds hReach)

theorem pythonReachableFromInit_satisfies_atom_systemNoBadDebt
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    Relational.Satisfies simplexBorrowStepRel simplexBorrowValuation state
      (.atom .systemNoBadDebt) := by
  simpa [Relational.Satisfies, Relational.eval] using
    (pythonReachableFromInit_implies_systemNoBadDebt_at_quoted hReach)

theorem pythonReachableFromInit_satisfies_box_systemNoBadDebt
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    Relational.Satisfies simplexBorrowStepRel simplexBorrowValuation state
      (Relational.ModalFormula.box (.atom .systemNoBadDebt)) := by
  rw [Relational.Satisfies, Relational.eval_box]
  refine (Relational.mem_box_iff
    (r := Relational.converse simplexBorrowStepRel)
    (s := simplexBorrowValuation .systemNoBadDebt)
    (b := state)).2 ?_
  intro next hNext
  exact simplexBorrowStepRel_successor_systemNoBadDebt hReach hNext

/-- Reachable-state safety envelope on the concrete `SimplexBorrow` modal model. -/
def simplexBorrowSafetyFormula : Relational.ModalFormula SimplexBorrowAtom :=
  Relational.ModalFormula.inf
    (.atom .quotedInvariant)
    (Relational.ModalFormula.inf
      (.atom .bounds)
      (Relational.ModalFormula.box (.atom .systemNoBadDebt)))

theorem pythonReachableFromInit_satisfies_safetyFormula
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    Relational.Satisfies simplexBorrowStepRel simplexBorrowValuation state
      simplexBorrowSafetyFormula := by
  rw [Relational.Satisfies, simplexBorrowSafetyFormula, Relational.eval_inf]
  refine ⟨pythonReachableFromInit_satisfies_atom_quotedInvariant hReach, ?_⟩
  rw [Relational.eval_inf]
  exact ⟨pythonReachableFromInit_satisfies_atom_bounds hReach,
    pythonReachableFromInit_satisfies_box_systemNoBadDebt hReach⟩

/-- Theory quotient of the concrete `SimplexBorrow` modal model. -/
abbrev SimplexBorrowTheoryQuotient :=
  Relational.TheoryQuotient simplexBorrowStepRel simplexBorrowValuation

/-- Canonical Stone clopen safety envelope on the `SimplexBorrow` theory quotient. -/
def simplexBorrowSafetyClopen :
    Set (Ultrafilter SimplexBorrowTheoryQuotient) :=
  Stone.formulaClopen simplexBorrowStepRel simplexBorrowValuation simplexBorrowSafetyFormula

theorem simplexBorrowSafetyClopen_mem_formulaClopenSubalgebra :
    simplexBorrowSafetyClopen ∈
      Stone.formulaClopenSubalgebra simplexBorrowStepRel simplexBorrowValuation := by
  exact Stone.formulaClopen_mem_formulaClopenSubalgebra
    simplexBorrowStepRel simplexBorrowValuation simplexBorrowSafetyFormula

theorem pythonReachableFromInit_mem_simplexBorrowSafetyClopen
    {state : SimplexBorrowState}
    (hReach : pythonReachableFromInit state) :
    Stone.principalPoint
        (Relational.theoryQuotientMk simplexBorrowStepRel simplexBorrowValuation state) ∈
      simplexBorrowSafetyClopen := by
  exact
    (Stone.principalPoint_mem_formulaClopen_mk_iff
      simplexBorrowStepRel simplexBorrowValuation state simplexBorrowSafetyFormula).2 <|
      pythonReachableFromInit_satisfies_safetyFormula hReach

end LeanMathlib
