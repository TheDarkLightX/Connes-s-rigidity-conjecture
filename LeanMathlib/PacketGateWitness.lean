import LeanMathlib.PacketGates
import LeanMathlib.Order.SymmDiffBihimpWitness

namespace LeanMathlib

open scoped symmDiff

/--
Set-level disagreement certificate derived from the local Boolean witness
library: two sets differ iff some element lies in their symmetric difference.
-/
theorem set_ne_iff_exists_mem_symmDiff {α : Type*} (s t : Set α) :
    s ≠ t ↔ ∃ a : α, a ∈ s ∆ t := by
  constructor
  · intro hst
    rcases (ne_iff_exists_atom_disjoint_bihimp (a := s) (b := t)).1 hst with ⟨p, hp, hpd⟩
    rcases Set.isAtom_iff.1 hp with ⟨a, rfl⟩
    have hsubset : ({a} : Set α) ≤ s ∆ t :=
      (le_symmDiff_iff_disjoint_bihimp (a := s) (b := t) (p := {a})).2 hpd
    exact ⟨a, hsubset (by simp)⟩
  · rintro ⟨a, ha⟩ hEq
    simp [hEq] at ha

inductive SettlementValueFlag
  | lpMode
  | attestationMode
  | priceProvenanceOk
  | attestationOk
  | assetConservationOk
  | lpLiabilityBalancedOk
  | valueConservationOk
  deriving DecidableEq, Fintype, Repr

def activeSettlementValueFlags (inputs : SettlementValueInputs) : Set SettlementValueFlag
  | .lpMode => inputs.lpMode = true
  | .attestationMode => inputs.attestationMode = true
  | .priceProvenanceOk => inputs.priceProvenanceOk = true
  | .attestationOk => inputs.attestationOk = true
  | .assetConservationOk => inputs.assetConservationOk = true
  | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = true
  | .valueConservationOk => inputs.valueConservationOk = true

@[simp] theorem mem_activeSettlementValueFlags
    (inputs : SettlementValueInputs) (flag : SettlementValueFlag) :
    flag ∈ activeSettlementValueFlags inputs ↔
      match flag with
      | .lpMode => inputs.lpMode = true
      | .attestationMode => inputs.attestationMode = true
      | .priceProvenanceOk => inputs.priceProvenanceOk = true
      | .attestationOk => inputs.attestationOk = true
      | .assetConservationOk => inputs.assetConservationOk = true
      | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = true
      | .valueConservationOk => inputs.valueConservationOk = true := Iff.rfl

theorem settlementValueGate_eq_of_activeFlags_eq
    {x y : SettlementValueInputs}
    (hxy : activeSettlementValueFlags x = activeSettlementValueFlags y) :
    settlementValueGate x = settlementValueGate y := by
  have hLpMode : x.lpMode = y.lpMode := by
    have := congrArg (fun s : Set SettlementValueFlag => SettlementValueFlag.lpMode ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  have hAttestationMode : x.attestationMode = y.attestationMode := by
    have := congrArg
      (fun s : Set SettlementValueFlag => SettlementValueFlag.attestationMode ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  have hPriceProvenance : x.priceProvenanceOk = y.priceProvenanceOk := by
    have := congrArg
      (fun s : Set SettlementValueFlag => SettlementValueFlag.priceProvenanceOk ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  have hAttestation : x.attestationOk = y.attestationOk := by
    have := congrArg
      (fun s : Set SettlementValueFlag => SettlementValueFlag.attestationOk ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  have hAsset : x.assetConservationOk = y.assetConservationOk := by
    have := congrArg
      (fun s : Set SettlementValueFlag => SettlementValueFlag.assetConservationOk ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  have hLiability : x.lpLiabilityBalancedOk = y.lpLiabilityBalancedOk := by
    have := congrArg
      (fun s : Set SettlementValueFlag => SettlementValueFlag.lpLiabilityBalancedOk ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  have hValue : x.valueConservationOk = y.valueConservationOk := by
    have := congrArg
      (fun s : Set SettlementValueFlag => SettlementValueFlag.valueConservationOk ∈ s) hxy
    simpa [activeSettlementValueFlags] using this
  simp [settlementValueGate, optionalGate, hLpMode, hAttestationMode, hPriceProvenance,
    hAttestation, hAsset, hLiability, hValue]

theorem activeSettlementValueFlags_ne_iff_exists_mem_symmDiff
    (x y : SettlementValueInputs) :
    activeSettlementValueFlags x ≠ activeSettlementValueFlags y ↔
      ∃ flag : SettlementValueFlag,
        flag ∈ activeSettlementValueFlags x ∆ activeSettlementValueFlags y := by
  simpa using
    (set_ne_iff_exists_mem_symmDiff
      (s := activeSettlementValueFlags x)
      (t := activeSettlementValueFlags y))

theorem exists_settlementValue_flag_witness_of_gate_ne
    {x y : SettlementValueInputs}
    (hxy : settlementValueGate x ≠ settlementValueGate y) :
    ∃ flag : SettlementValueFlag,
      flag ∈ activeSettlementValueFlags x ∆ activeSettlementValueFlags y := by
  have hset : activeSettlementValueFlags x ≠ activeSettlementValueFlags y := by
    intro hEq
    exact hxy (settlementValueGate_eq_of_activeFlags_eq hEq)
  exact (activeSettlementValueFlags_ne_iff_exists_mem_symmDiff x y).1 hset

inductive FeatureExtensionFlag
  | buybackFloorOk
  | buybackFloorFixedpointOk
  | rebateOk
  | lockWeightOk
  deriving DecidableEq, Fintype, Repr

def activeFeatureExtensionFlags (inputs : FeatureExtensionInputs) : Set FeatureExtensionFlag
  | .buybackFloorOk => inputs.buybackFloorOk = true
  | .buybackFloorFixedpointOk => inputs.buybackFloorFixedpointOk = true
  | .rebateOk => inputs.rebateOk = true
  | .lockWeightOk => inputs.lockWeightOk = true

@[simp] theorem mem_activeFeatureExtensionFlags
    (inputs : FeatureExtensionInputs) (flag : FeatureExtensionFlag) :
    flag ∈ activeFeatureExtensionFlags inputs ↔
      match flag with
      | .buybackFloorOk => inputs.buybackFloorOk = true
      | .buybackFloorFixedpointOk => inputs.buybackFloorFixedpointOk = true
      | .rebateOk => inputs.rebateOk = true
      | .lockWeightOk => inputs.lockWeightOk = true := Iff.rfl

theorem featureExtensionGate_eq_of_activeFlags_eq
    {x y : FeatureExtensionInputs}
    (hxy : activeFeatureExtensionFlags x = activeFeatureExtensionFlags y) :
    featureExtensionGate x = featureExtensionGate y := by
  have hBuyback : x.buybackFloorOk = y.buybackFloorOk := by
    have := congrArg
      (fun s : Set FeatureExtensionFlag => FeatureExtensionFlag.buybackFloorOk ∈ s) hxy
    simpa [activeFeatureExtensionFlags] using this
  have hFixedpoint : x.buybackFloorFixedpointOk = y.buybackFloorFixedpointOk := by
    have := congrArg
      (fun s : Set FeatureExtensionFlag => FeatureExtensionFlag.buybackFloorFixedpointOk ∈ s) hxy
    simpa [activeFeatureExtensionFlags] using this
  have hRebate : x.rebateOk = y.rebateOk := by
    have := congrArg
      (fun s : Set FeatureExtensionFlag => FeatureExtensionFlag.rebateOk ∈ s) hxy
    simpa [activeFeatureExtensionFlags] using this
  have hLockWeight : x.lockWeightOk = y.lockWeightOk := by
    have := congrArg (fun s : Set FeatureExtensionFlag => FeatureExtensionFlag.lockWeightOk ∈ s) hxy
    simpa [activeFeatureExtensionFlags] using this
  simp [featureExtensionGate, hBuyback, hFixedpoint, hRebate, hLockWeight]

theorem activeFeatureExtensionFlags_ne_iff_exists_mem_symmDiff
    (x y : FeatureExtensionInputs) :
    activeFeatureExtensionFlags x ≠ activeFeatureExtensionFlags y ↔
      ∃ flag : FeatureExtensionFlag,
        flag ∈ activeFeatureExtensionFlags x ∆ activeFeatureExtensionFlags y := by
  simpa using
    (set_ne_iff_exists_mem_symmDiff
      (s := activeFeatureExtensionFlags x)
      (t := activeFeatureExtensionFlags y))

theorem exists_featureExtension_flag_witness_of_gate_ne
    {x y : FeatureExtensionInputs}
    (hxy : featureExtensionGate x ≠ featureExtensionGate y) :
    ∃ flag : FeatureExtensionFlag,
      flag ∈ activeFeatureExtensionFlags x ∆ activeFeatureExtensionFlags y := by
  have hset : activeFeatureExtensionFlags x ≠ activeFeatureExtensionFlags y := by
    intro hEq
    exact hxy (featureExtensionGate_eq_of_activeFlags_eq hEq)
  exact (activeFeatureExtensionFlags_ne_iff_exists_mem_symmDiff x y).1 hset

inductive SettlementEndToEndGateFlag
  | attestationMode
  | strongCertificateOk
  | featureExtensionPacketOk
  | moduleBundleOk
  | fullPriceRailsOk
  | priceProvenanceOk
  | attestationOk
  | assetConservationOk
  | lpLiabilityBalancedOk
  | valueConservationOk
  deriving DecidableEq, Fintype, Repr

/--
Gate-relevant observable surface for the end-to-end settlement packet.

`endogenousLpMode` is deliberately omitted because the curated gate is
independent of it.
-/
def activeSettlementEndToEndGateFlags
    (inputs : SettlementEndToEndInputs) : Set SettlementEndToEndGateFlag
  | .attestationMode => inputs.attestationMode = true
  | .strongCertificateOk => inputs.strongCertificateOk = true
  | .featureExtensionPacketOk => inputs.featureExtensionPacketOk = true
  | .moduleBundleOk => inputs.moduleBundleOk = true
  | .fullPriceRailsOk => inputs.fullPriceRailsOk = true
  | .priceProvenanceOk => inputs.priceProvenanceOk = true
  | .attestationOk => inputs.attestationOk = true
  | .assetConservationOk => inputs.assetConservationOk = true
  | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = true
  | .valueConservationOk => inputs.valueConservationOk = true

@[simp] theorem mem_activeSettlementEndToEndGateFlags
    (inputs : SettlementEndToEndInputs) (flag : SettlementEndToEndGateFlag) :
    flag ∈ activeSettlementEndToEndGateFlags inputs ↔
      match flag with
      | .attestationMode => inputs.attestationMode = true
      | .strongCertificateOk => inputs.strongCertificateOk = true
      | .featureExtensionPacketOk => inputs.featureExtensionPacketOk = true
      | .moduleBundleOk => inputs.moduleBundleOk = true
      | .fullPriceRailsOk => inputs.fullPriceRailsOk = true
      | .priceProvenanceOk => inputs.priceProvenanceOk = true
      | .attestationOk => inputs.attestationOk = true
      | .assetConservationOk => inputs.assetConservationOk = true
      | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = true
      | .valueConservationOk => inputs.valueConservationOk = true := Iff.rfl

theorem activeSettlementEndToEndGateFlags_endogenousLpMode_irrelevant
    (inputs : SettlementEndToEndInputs) (flag : Bool) :
    activeSettlementEndToEndGateFlags { inputs with endogenousLpMode := flag } =
      activeSettlementEndToEndGateFlags inputs := by
  rfl

theorem settlementEndToEndGate_eq_of_activeFlags_eq
    {x y : SettlementEndToEndInputs}
    (hxy : activeSettlementEndToEndGateFlags x = activeSettlementEndToEndGateFlags y) :
    settlementEndToEndGate x = settlementEndToEndGate y := by
  have hAttestationMode : x.attestationMode = y.attestationMode := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag => SettlementEndToEndGateFlag.attestationMode ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hStrongCertificate : x.strongCertificateOk = y.strongCertificateOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.strongCertificateOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hFeatureExtension : x.featureExtensionPacketOk = y.featureExtensionPacketOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.featureExtensionPacketOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hModuleBundle : x.moduleBundleOk = y.moduleBundleOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.moduleBundleOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hFullPriceRails : x.fullPriceRailsOk = y.fullPriceRailsOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.fullPriceRailsOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hPriceProvenance : x.priceProvenanceOk = y.priceProvenanceOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.priceProvenanceOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hAttestation : x.attestationOk = y.attestationOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag => SettlementEndToEndGateFlag.attestationOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hAsset : x.assetConservationOk = y.assetConservationOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.assetConservationOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hLiability : x.lpLiabilityBalancedOk = y.lpLiabilityBalancedOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.lpLiabilityBalancedOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  have hValue : x.valueConservationOk = y.valueConservationOk := by
    have := congrArg
      (fun s : Set SettlementEndToEndGateFlag =>
        SettlementEndToEndGateFlag.valueConservationOk ∈ s) hxy
    simpa [activeSettlementEndToEndGateFlags] using this
  simp [settlementEndToEndGate, optionalGate, hAttestationMode, hStrongCertificate,
    hFeatureExtension, hModuleBundle, hFullPriceRails, hPriceProvenance, hAttestation,
    hAsset, hLiability, hValue]

theorem activeSettlementEndToEndGateFlags_ne_iff_exists_mem_symmDiff
    (x y : SettlementEndToEndInputs) :
    activeSettlementEndToEndGateFlags x ≠ activeSettlementEndToEndGateFlags y ↔
      ∃ flag : SettlementEndToEndGateFlag,
        flag ∈ activeSettlementEndToEndGateFlags x ∆ activeSettlementEndToEndGateFlags y := by
  simpa using
    (set_ne_iff_exists_mem_symmDiff
      (s := activeSettlementEndToEndGateFlags x)
      (t := activeSettlementEndToEndGateFlags y))

theorem exists_settlementEndToEnd_flag_witness_of_gate_ne
    {x y : SettlementEndToEndInputs}
    (hxy : settlementEndToEndGate x ≠ settlementEndToEndGate y) :
    ∃ flag : SettlementEndToEndGateFlag,
      flag ∈ activeSettlementEndToEndGateFlags x ∆ activeSettlementEndToEndGateFlags y := by
  have hset : activeSettlementEndToEndGateFlags x ≠ activeSettlementEndToEndGateFlags y := by
    intro hEq
    exact hxy (settlementEndToEndGate_eq_of_activeFlags_eq hEq)
  exact (activeSettlementEndToEndGateFlags_ne_iff_exists_mem_symmDiff x y).1 hset

end LeanMathlib
