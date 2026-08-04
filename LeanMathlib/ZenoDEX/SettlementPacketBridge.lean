import LeanMathlib.PacketGateBlockers

namespace LeanMathlib

open scoped symmDiff

namespace UpstreamMirror
namespace TauSwap

namespace SettlementValuePacket

structure Inputs where
  lpMode : Bool
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  lpMode : Bool
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    lpMode := inputs.lpMode
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
    packetOk :=
      inputs.priceProvenanceOk &&
      inputs.assetConservationOk &&
      inputs.valueConservationOk &&
      (if inputs.lpMode then inputs.lpLiabilityBalancedOk else true) &&
      (if inputs.attestationMode then inputs.attestationOk else true)
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

def toCurated (inputs : Inputs) : SettlementValueInputs :=
  {
    lpMode := inputs.lpMode
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
  }

@[simp] theorem buildPacket_packetOk_eq_curatedGate (inputs : Inputs) :
    (buildPacket inputs).packetOk = settlementValueGate (toCurated inputs) := by
  rfl

@[simp] theorem buildPacket_packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      ∀ flag : SettlementValueFlag,
        flag ∉ settlementValueBlockingFlags (toCurated inputs) := by
  simpa using
    (settlementValueGate_eq_true_iff_no_blockers (inputs := toCurated inputs))

@[simp] theorem buildPacket_packetOk_eq_false_iff_exists_blocker (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔
      ∃ flag : SettlementValueFlag,
        flag ∈ settlementValueBlockingFlags (toCurated inputs) := by
  simpa using
    (settlementValueGate_eq_false_iff_exists_blocker (inputs := toCurated inputs))

theorem exists_flag_witness_of_packetOk_ne {x y : Inputs}
    (hxy : (buildPacket x).packetOk ≠ (buildPacket y).packetOk) :
    ∃ flag : SettlementValueFlag,
      flag ∈ activeSettlementValueFlags (toCurated x) ∆
        activeSettlementValueFlags (toCurated y) := by
  exact exists_settlementValue_flag_witness_of_gate_ne <|
    by simpa using hxy

end SettlementValuePacket

namespace SettlementFeatureExtensionPacket

structure Inputs where
  buybackFloorOk : Bool
  buybackFloorFixedpointOk : Bool
  rebateOk : Bool
  lockWeightOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  buybackFloorOk : Bool
  buybackFloorFixedpointOk : Bool
  rebateOk : Bool
  lockWeightOk : Bool
  featureExtensionOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    buybackFloorOk := inputs.buybackFloorOk
    buybackFloorFixedpointOk := inputs.buybackFloorFixedpointOk
    rebateOk := inputs.rebateOk
    lockWeightOk := inputs.lockWeightOk
    featureExtensionOk :=
      inputs.buybackFloorOk &&
      inputs.buybackFloorFixedpointOk &&
      inputs.rebateOk &&
      inputs.lockWeightOk
    packetOk :=
      inputs.buybackFloorOk &&
      inputs.buybackFloorFixedpointOk &&
      inputs.rebateOk &&
      inputs.lockWeightOk
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

def toCurated (inputs : Inputs) : FeatureExtensionInputs :=
  {
    buybackFloorOk := inputs.buybackFloorOk
    buybackFloorFixedpointOk := inputs.buybackFloorFixedpointOk
    rebateOk := inputs.rebateOk
    lockWeightOk := inputs.lockWeightOk
  }

@[simp] theorem buildPacket_featureExtensionOk_eq_packetOk (inputs : Inputs) :
    (buildPacket inputs).featureExtensionOk = (buildPacket inputs).packetOk := by
  rfl

@[simp] theorem buildPacket_packetOk_eq_curatedGate (inputs : Inputs) :
    (buildPacket inputs).packetOk = featureExtensionGate (toCurated inputs) := by
  rfl

@[simp] theorem buildPacket_packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      ∀ flag : FeatureExtensionFlag,
        flag ∉ featureExtensionBlockingFlags (toCurated inputs) := by
  simpa using
    (featureExtensionGate_eq_true_iff_no_blockers (inputs := toCurated inputs))

@[simp] theorem buildPacket_packetOk_eq_false_iff_exists_blocker (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔
      ∃ flag : FeatureExtensionFlag,
        flag ∈ featureExtensionBlockingFlags (toCurated inputs) := by
  simpa using
    (featureExtensionGate_eq_false_iff_exists_blocker (inputs := toCurated inputs))

theorem exists_flag_witness_of_packetOk_ne {x y : Inputs}
    (hxy : (buildPacket x).packetOk ≠ (buildPacket y).packetOk) :
    ∃ flag : FeatureExtensionFlag,
      flag ∈ activeFeatureExtensionFlags (toCurated x) ∆
        activeFeatureExtensionFlags (toCurated y) := by
  exact exists_featureExtension_flag_witness_of_gate_ne <|
    by simpa using hxy

end SettlementFeatureExtensionPacket

namespace SettlementEndToEndCertificatePacket

structure Inputs where
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

structure Packet where
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
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    attestationMode := inputs.attestationMode
    endogenousLpMode := inputs.endogenousLpMode
    strongCertificateOk := inputs.strongCertificateOk
    featureExtensionPacketOk := inputs.featureExtensionPacketOk
    moduleBundleOk := inputs.moduleBundleOk
    fullPriceRailsOk := inputs.fullPriceRailsOk
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
    packetOk :=
      inputs.strongCertificateOk &&
      inputs.featureExtensionPacketOk &&
      inputs.moduleBundleOk &&
      inputs.fullPriceRailsOk &&
      inputs.priceProvenanceOk &&
      inputs.assetConservationOk &&
      inputs.valueConservationOk &&
      inputs.lpLiabilityBalancedOk &&
      (if inputs.attestationMode then inputs.attestationOk else true)
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

def toCurated (inputs : Inputs) : SettlementEndToEndInputs :=
  {
    attestationMode := inputs.attestationMode
    endogenousLpMode := inputs.endogenousLpMode
    strongCertificateOk := inputs.strongCertificateOk
    featureExtensionPacketOk := inputs.featureExtensionPacketOk
    moduleBundleOk := inputs.moduleBundleOk
    fullPriceRailsOk := inputs.fullPriceRailsOk
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
  }

@[simp] theorem buildPacket_packetOk_eq_curatedGate (inputs : Inputs) :
    (buildPacket inputs).packetOk = settlementEndToEndGate (toCurated inputs) := by
  rfl

@[simp] theorem buildPacket_packetOk_endogenousLpMode_irrelevant
    (inputs : Inputs) (flag : Bool) :
    (buildPacket { inputs with endogenousLpMode := flag }).packetOk =
      (buildPacket inputs).packetOk := by
  rfl

@[simp] theorem buildPacket_packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      ∀ flag : SettlementEndToEndGateFlag,
        flag ∉ settlementEndToEndBlockingFlags (toCurated inputs) := by
  simpa using
    (settlementEndToEndGate_eq_true_iff_no_blockers (inputs := toCurated inputs))

@[simp] theorem buildPacket_packetOk_eq_false_iff_exists_blocker (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔
      ∃ flag : SettlementEndToEndGateFlag,
        flag ∈ settlementEndToEndBlockingFlags (toCurated inputs) := by
  simpa using
    (settlementEndToEndGate_eq_false_iff_exists_blocker (inputs := toCurated inputs))

theorem exists_flag_witness_of_packetOk_ne {x y : Inputs}
    (hxy : (buildPacket x).packetOk ≠ (buildPacket y).packetOk) :
    ∃ flag : SettlementEndToEndGateFlag,
      flag ∈ activeSettlementEndToEndGateFlags (toCurated x) ∆
        activeSettlementEndToEndGateFlags (toCurated y) := by
  exact exists_settlementEndToEnd_flag_witness_of_gate_ne <|
    by simpa using hxy

end SettlementEndToEndCertificatePacket

end TauSwap
end UpstreamMirror

end LeanMathlib
