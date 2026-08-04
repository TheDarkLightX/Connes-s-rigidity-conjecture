import Mathlib

namespace LeanMathlib

/--
Priority-ordered actions extracted from the Tau lending-risk safe-table
experiment. The intent is to make the policy layer itself replayable and
reusable inside later lending and oracle proofs.
-/
inductive LendingRiskAction
  | freezeMarket
  | quarantineOracle
  | pauseBorrow
  | capLiquidation
  | governanceReview
  | allow
  | deny
  deriving DecidableEq, Repr

/--
Priority decision surface for lending-risk alarms.

This is the exact ordering used by the Tau safe-table example:

- exploit witness
- oracle divergence
- solvency gap
- liquidation cascade
- governance override
- healthy
- deny

Higher-priority alarms strictly dominate lower-priority ones.
-/
def lendingRiskDecision
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) : LendingRiskAction :=
  if exploitWitness then
    .freezeMarket
  else if oracleDivergence then
    .quarantineOracle
  else if solvencyGap then
    .pauseBorrow
  else if liquidationCascade then
    .capLiquidation
  else if governanceOverride then
    .governanceReview
  else if healthy then
    .allow
  else
    .deny

@[simp] theorem lendingRiskDecision_eq_freezeMarket_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .freezeMarket ↔
      exploitWitness = true := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

@[simp] theorem lendingRiskDecision_eq_quarantineOracle_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .quarantineOracle ↔
      exploitWitness = false ∧ oracleDivergence = true := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

@[simp] theorem lendingRiskDecision_eq_pauseBorrow_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .pauseBorrow ↔
      exploitWitness = false ∧
      oracleDivergence = false ∧
      solvencyGap = true := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

@[simp] theorem lendingRiskDecision_eq_capLiquidation_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .capLiquidation ↔
      exploitWitness = false ∧
      oracleDivergence = false ∧
      solvencyGap = false ∧
      liquidationCascade = true := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

@[simp] theorem lendingRiskDecision_eq_governanceReview_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .governanceReview ↔
      exploitWitness = false ∧
      oracleDivergence = false ∧
      solvencyGap = false ∧
      liquidationCascade = false ∧
      governanceOverride = true := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

@[simp] theorem lendingRiskDecision_eq_allow_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .allow ↔
      exploitWitness = false ∧
      oracleDivergence = false ∧
      solvencyGap = false ∧
      liquidationCascade = false ∧
      governanceOverride = false ∧
      healthy = true := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

@[simp] theorem lendingRiskDecision_eq_deny_iff
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .deny ↔
      exploitWitness = false ∧
      oracleDivergence = false ∧
      solvencyGap = false ∧
      liquidationCascade = false ∧
      governanceOverride = false ∧
      healthy = false := by
  cases exploitWitness <;>
    cases oracleDivergence <;>
    cases solvencyGap <;>
    cases liquidationCascade <;>
    cases governanceOverride <;>
    cases healthy <;>
    decide

/--
Any high-priority alarm blocks the `allow` branch, even when the `healthy`
signal is also present.
-/
theorem lendingRiskDecision_ne_allow_of_highPriorityAlarm
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (h :
      exploitWitness = true ∨
      oracleDivergence = true ∨
      solvencyGap = true ∨
      liquidationCascade = true) :
    lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy ≠ .allow := by
  intro hAllow
  rcases (lendingRiskDecision_eq_allow_iff
    exploitWitness oracleDivergence solvencyGap liquidationCascade
    governanceOverride healthy).1 hAllow with
      ⟨hExploit, hOracle, hSolvency, hCascade, _, _⟩
  rcases h with hExploit' | hRest
  · cases hExploit.symm.trans hExploit'
  · rcases hRest with hOracle' | hRest
    · cases hOracle.symm.trans hOracle'
    · rcases hRest with hSolvency' | hCascade'
      · cases hSolvency.symm.trans hSolvency'
      · cases hCascade.symm.trans hCascade'

end LeanMathlib
