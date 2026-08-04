import Mathlib

namespace LeanMathlib

/--
`optionalGate enabled check` models a boolean gate that is only enforced when
the corresponding mode is enabled.

This captures the recurring "if feature is on, the witness must validate;
otherwise the gate is vacuously open" pattern that shows up across packet-style
proofs.
-/
def optionalGate (enabled check : Bool) : Bool :=
  if enabled then check else true

@[simp] theorem optionalGate_eq_true_iff (enabled check : Bool) :
    optionalGate enabled check = true ↔ enabled = false ∨ check = true := by
  cases enabled <;> simp [optionalGate]

/--
Reusable normalization lemma for a packet gate with three required checks and
two optional feature-dependent checks.
-/
theorem required3Optional2_eq_true_iff
    (a b c enabled₁ check₁ enabled₂ check₂ : Bool) :
    (a && b && c && optionalGate enabled₁ check₁ && optionalGate enabled₂ check₂) = true ↔
      a = true ∧
      b = true ∧
      c = true ∧
      (enabled₁ = false ∨ check₁ = true) ∧
      (enabled₂ = false ∨ check₂ = true) := by
  simp [and_assoc]

/--
Reusable normalization lemma for a packet gate that is just a conjunction of
four mandatory checks.
-/
theorem required4_eq_true_iff (a b c d : Bool) :
    (a && b && c && d) = true ↔
      a = true ∧ b = true ∧ c = true ∧ d = true := by
  simp [and_assoc]

/--
Curated shell for the settlement-value gate. This mirrors the shape of the
existing ZenoDEX settlement value packet, but is phrased here as a reusable
boolean gate theorem rather than a per-file exhaustive case split.
-/
structure SettlementValueInputs where
  lpMode : Bool
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

def settlementValueGate (inputs : SettlementValueInputs) : Bool :=
  inputs.priceProvenanceOk &&
    inputs.assetConservationOk &&
    inputs.valueConservationOk &&
    optionalGate inputs.lpMode inputs.lpLiabilityBalancedOk &&
    optionalGate inputs.attestationMode inputs.attestationOk

theorem settlementValueGate_eq_true_iff (inputs : SettlementValueInputs) :
    settlementValueGate inputs = true ↔
      inputs.priceProvenanceOk = true ∧
      inputs.assetConservationOk = true ∧
      inputs.valueConservationOk = true ∧
      (inputs.lpMode = false ∨ inputs.lpLiabilityBalancedOk = true) ∧
      (inputs.attestationMode = false ∨ inputs.attestationOk = true) := by
  simpa [settlementValueGate] using
    required3Optional2_eq_true_iff
      inputs.priceProvenanceOk
      inputs.assetConservationOk
      inputs.valueConservationOk
      inputs.lpMode
      inputs.lpLiabilityBalancedOk
      inputs.attestationMode
      inputs.attestationOk

/--
Curated shell for a four-check feature-extension gate.
-/
structure FeatureExtensionInputs where
  buybackFloorOk : Bool
  buybackFloorFixedpointOk : Bool
  rebateOk : Bool
  lockWeightOk : Bool
  deriving DecidableEq, Repr

def featureExtensionGate (inputs : FeatureExtensionInputs) : Bool :=
  inputs.buybackFloorOk &&
    inputs.buybackFloorFixedpointOk &&
    inputs.rebateOk &&
    inputs.lockWeightOk

theorem featureExtensionGate_eq_true_iff (inputs : FeatureExtensionInputs) :
    featureExtensionGate inputs = true ↔
      inputs.buybackFloorOk = true ∧
      inputs.buybackFloorFixedpointOk = true ∧
      inputs.rebateOk = true ∧
      inputs.lockWeightOk = true := by
  simpa [featureExtensionGate] using
    required4_eq_true_iff
      inputs.buybackFloorOk
      inputs.buybackFloorFixedpointOk
      inputs.rebateOk
      inputs.lockWeightOk

/--
Curated shell for the replayable end-to-end settlement gate. This captures the
boolean acceptance surface while making the currently unused
`endogenousLpMode` parameter explicit.
-/
structure SettlementEndToEndInputs where
  attestationMode : Bool
  endogenousLpMode : Bool
  strongCertificateOk : Bool
  featureExtensionPacketOk : Bool
  moduleBundleOk : Bool
  fullPriceRailsOk : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

def settlementEndToEndGate (inputs : SettlementEndToEndInputs) : Bool :=
  inputs.strongCertificateOk &&
    inputs.featureExtensionPacketOk &&
    inputs.moduleBundleOk &&
    inputs.fullPriceRailsOk &&
    inputs.priceProvenanceOk &&
    inputs.assetConservationOk &&
    inputs.valueConservationOk &&
    inputs.lpLiabilityBalancedOk &&
    optionalGate inputs.attestationMode inputs.attestationOk

theorem settlementEndToEndGate_eq_true_iff (inputs : SettlementEndToEndInputs) :
    settlementEndToEndGate inputs = true ↔
      inputs.strongCertificateOk = true ∧
      inputs.featureExtensionPacketOk = true ∧
      inputs.moduleBundleOk = true ∧
      inputs.fullPriceRailsOk = true ∧
      inputs.priceProvenanceOk = true ∧
      inputs.assetConservationOk = true ∧
      inputs.valueConservationOk = true ∧
      inputs.lpLiabilityBalancedOk = true ∧
      (inputs.attestationMode = false ∨ inputs.attestationOk = true) := by
  simp [settlementEndToEndGate, optionalGate, and_assoc]

/--
The end-to-end gate is currently independent of `endogenousLpMode`. Recording
that fact explicitly makes future semantic drift visible.
-/
theorem settlementEndToEndGate_endogenousLpMode_irrelevant
    (inputs : SettlementEndToEndInputs) (flag : Bool) :
    settlementEndToEndGate { inputs with endogenousLpMode := flag } =
      settlementEndToEndGate inputs := by
  rfl

end LeanMathlib
