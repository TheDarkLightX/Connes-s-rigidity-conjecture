import Mathlib
import LeanMathlib.DeFi.LiquidationCaps

namespace LeanMathlib

/--
An exploit witness forces the blocking liquidation policy.
-/
theorem policyTransfer_eq_noLiquidation_of_exploitWitness
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = true) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      noLiquidation := by
  apply policyTransfer_eq_noLiquidation_of_blocksLiquidation
  left
  rw [lendingRiskDecision_eq_freezeMarket_iff]
  exact hExploit

/--
If there is no exploit witness, an oracle-divergence alarm also forces the
blocking liquidation policy.
-/
theorem policyTransfer_eq_noLiquidation_of_oracleDivergence
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = true) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      noLiquidation := by
  apply policyTransfer_eq_noLiquidation_of_blocksLiquidation
  right
  left
  rw [lendingRiskDecision_eq_quarantineOracle_iff]
  exact ⟨hExploit, hOracle⟩

/--
When solvency gap is the highest-priority active alarm, liquidation remains on
the uncapped path while new borrowing is paused.
-/
theorem policyTransfer_eq_uncapped_of_pauseBorrowDecision
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = false)
    (hSolvency : solvencyGap = true) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      uncapped := by
  have hDecision :
      lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .pauseBorrow := by
    rw [lendingRiskDecision_eq_pauseBorrow_iff]
    exact ⟨hExploit, hOracle, hSolvency⟩
  rw [hDecision]
  rfl

/--
When liquidation cascade is the highest-priority active alarm, the capped
liquidation path is selected.
-/
theorem policyTransfer_eq_capped_of_capLiquidationDecision
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = false)
    (hSolvency : solvencyGap = false)
    (hCascade : liquidationCascade = true) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      capped := by
  have hDecision :
      lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .capLiquidation := by
    rw [lendingRiskDecision_eq_capLiquidation_iff]
    exact ⟨hExploit, hOracle, hSolvency, hCascade⟩
  rw [hDecision]
  rfl

/--
Governance review also blocks liquidation if it is the first active alarm after
the higher-priority checks are clear.
-/
theorem policyTransfer_eq_noLiquidation_of_governanceReviewDecision
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = false)
    (hSolvency : solvencyGap = false)
    (hCascade : liquidationCascade = false)
    (hGovernance : governanceOverride = true) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      noLiquidation := by
  apply policyTransfer_eq_noLiquidation_of_blocksLiquidation
  right
  right
  left
  rw [lendingRiskDecision_eq_governanceReview_iff]
  exact ⟨hExploit, hOracle, hSolvency, hCascade, hGovernance⟩

/--
If every higher-priority alarm is clear and the position is healthy, the
uncapped transfer path is selected.
-/
theorem policyTransfer_eq_uncapped_of_allowDecision
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = false)
    (hSolvency : solvencyGap = false)
    (hCascade : liquidationCascade = false)
    (hGovernance : governanceOverride = false)
    (hHealthy : healthy = true) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      uncapped := by
  have hDecision :
      lendingRiskDecision exploitWitness oracleDivergence solvencyGap
        liquidationCascade governanceOverride healthy = .allow := by
    rw [lendingRiskDecision_eq_allow_iff]
    exact ⟨hExploit, hOracle, hSolvency, hCascade, hGovernance, hHealthy⟩
  rw [hDecision]
  rfl

/--
If every higher-priority alarm is clear and the position is not healthy, the
deny branch blocks liquidation.
-/
theorem policyTransfer_eq_noLiquidation_of_denyDecision
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = false)
    (hSolvency : solvencyGap = false)
    (hCascade : liquidationCascade = false)
    (hGovernance : governanceOverride = false)
    (hHealthy : healthy = false) :
    policyTransfer
        (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
          liquidationCascade governanceOverride healthy)
        capped uncapped =
      noLiquidation := by
  apply policyTransfer_eq_noLiquidation_of_blocksLiquidation
  right
  right
  right
  rw [lendingRiskDecision_eq_deny_iff]
  exact ⟨hExploit, hOracle, hSolvency, hCascade, hGovernance, hHealthy⟩

/--
Exploit witnesses leave the solvency margin unchanged because liquidation is
blocked.
-/
theorem postLiquidationSolvencyMargin_eq_pre_of_exploitWitness
    (position : LendingPosition)
    (price : Rat)
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = true) :
    postLiquidationSolvencyMargin
        position
        price
        (policyTransfer
          (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
            liquidationCascade governanceOverride healthy)
          capped uncapped) =
      solvencyMargin position price := by
  rw [policyTransfer_eq_noLiquidation_of_exploitWitness
    exploitWitness oracleDivergence solvencyGap liquidationCascade
    governanceOverride healthy capped uncapped hExploit]
  exact postLiquidationSolvencyMargin_eq_of_noLiquidation position price

/--
Oracle-divergence alarms also leave the solvency margin unchanged because the
liquidation path is blocked.
-/
theorem postLiquidationSolvencyMargin_eq_pre_of_oracleDivergence
    (position : LendingPosition)
    (price : Rat)
    (exploitWitness oracleDivergence solvencyGap liquidationCascade
      governanceOverride healthy : Bool)
    (capped uncapped : LiquidationTransfer)
    (hExploit : exploitWitness = false)
    (hOracle : oracleDivergence = true) :
    postLiquidationSolvencyMargin
        position
        price
        (policyTransfer
          (lendingRiskDecision exploitWitness oracleDivergence solvencyGap
            liquidationCascade governanceOverride healthy)
          capped uncapped) =
      solvencyMargin position price := by
  rw [policyTransfer_eq_noLiquidation_of_oracleDivergence
    exploitWitness oracleDivergence solvencyGap liquidationCascade
    governanceOverride healthy capped uncapped hExploit hOracle]
  exact postLiquidationSolvencyMargin_eq_of_noLiquidation position price

end LeanMathlib
