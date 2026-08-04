import LeanMathlib.PacketGateWitness

namespace LeanMathlib

def settlementValueBlockingFlags
    (inputs : SettlementValueInputs) : Set SettlementValueFlag
  | .lpMode => False
  | .attestationMode => False
  | .priceProvenanceOk => inputs.priceProvenanceOk = false
  | .attestationOk =>
      inputs.attestationMode = true ∧ inputs.attestationOk = false
  | .assetConservationOk => inputs.assetConservationOk = false
  | .lpLiabilityBalancedOk =>
      inputs.lpMode = true ∧ inputs.lpLiabilityBalancedOk = false
  | .valueConservationOk => inputs.valueConservationOk = false

@[simp] theorem mem_settlementValueBlockingFlags
    (inputs : SettlementValueInputs) (flag : SettlementValueFlag) :
    flag ∈ settlementValueBlockingFlags inputs ↔
      match flag with
      | .lpMode => False
      | .attestationMode => False
      | .priceProvenanceOk => inputs.priceProvenanceOk = false
      | .attestationOk =>
          inputs.attestationMode = true ∧ inputs.attestationOk = false
      | .assetConservationOk => inputs.assetConservationOk = false
      | .lpLiabilityBalancedOk =>
          inputs.lpMode = true ∧ inputs.lpLiabilityBalancedOk = false
      | .valueConservationOk => inputs.valueConservationOk = false := Iff.rfl

theorem settlementValueGate_eq_true_iff_no_blockers
    (inputs : SettlementValueInputs) :
    settlementValueGate inputs = true ↔
      ∀ flag : SettlementValueFlag, flag ∉ settlementValueBlockingFlags inputs := by
  constructor
  · intro hGate flag hBlock
    rcases (settlementValueGate_eq_true_iff inputs).1 hGate with
      ⟨hPrice, hAsset, hValue, hLpOptional, hAttOptional⟩
    cases flag with
    | lpMode =>
        simp at hBlock
    | attestationMode =>
        simp at hBlock
    | priceProvenanceOk =>
        simp [hPrice] at hBlock
    | attestationOk =>
        rcases hAttOptional with hModeFalse | hAttTrue
        · simp [hModeFalse] at hBlock
        · simp [hAttTrue] at hBlock
    | assetConservationOk =>
        simp [hAsset] at hBlock
    | lpLiabilityBalancedOk =>
        rcases hLpOptional with hModeFalse | hLiabilityTrue
        · simp [hModeFalse] at hBlock
        · simp [hLiabilityTrue] at hBlock
    | valueConservationOk =>
        simp [hValue] at hBlock
  · intro hNo
    have hPrice : inputs.priceProvenanceOk = true := by
      cases hPrice : inputs.priceProvenanceOk with
      | false =>
          exfalso
          exact hNo .priceProvenanceOk (by simp [hPrice])
      | true =>
          simp
    have hAsset : inputs.assetConservationOk = true := by
      cases hAsset : inputs.assetConservationOk with
      | false =>
          exfalso
          exact hNo .assetConservationOk (by simp [hAsset])
      | true =>
          simp
    have hValue : inputs.valueConservationOk = true := by
      cases hValue : inputs.valueConservationOk with
      | false =>
          exfalso
          exact hNo .valueConservationOk (by simp [hValue])
      | true =>
          simp
    have hLpOptional :
        inputs.lpMode = false ∨ inputs.lpLiabilityBalancedOk = true := by
      cases hMode : inputs.lpMode with
      | false =>
          simp
      | true =>
          cases hLiability : inputs.lpLiabilityBalancedOk with
          | false =>
              exfalso
              exact hNo .lpLiabilityBalancedOk
                (by simp [hMode, hLiability])
          | true =>
              simp
    have hAttOptional :
        inputs.attestationMode = false ∨ inputs.attestationOk = true := by
      cases hMode : inputs.attestationMode with
      | false =>
          simp
      | true =>
          cases hAtt : inputs.attestationOk with
          | false =>
              exfalso
              exact hNo .attestationOk
                (by simp [hMode, hAtt])
          | true =>
              simp
    exact (settlementValueGate_eq_true_iff inputs).2
      ⟨hPrice, hAsset, hValue, hLpOptional, hAttOptional⟩

theorem settlementValueGate_eq_false_iff_exists_blocker
    (inputs : SettlementValueInputs) :
    settlementValueGate inputs = false ↔
      ∃ flag : SettlementValueFlag, flag ∈ settlementValueBlockingFlags inputs := by
  constructor
  · intro hGate
    by_contra hNoExists
    have hNo :
        ∀ flag : SettlementValueFlag, flag ∉ settlementValueBlockingFlags inputs := by
      intro flag hFlag
      exact hNoExists ⟨flag, hFlag⟩
    have hTrue := (settlementValueGate_eq_true_iff_no_blockers inputs).2 hNo
    simp [hTrue] at hGate
  · rintro ⟨flag, hFlag⟩
    cases hGate : settlementValueGate inputs with
    | false =>
        simp
    | true =>
        exfalso
        exact (settlementValueGate_eq_true_iff_no_blockers inputs).1 hGate flag hFlag

def featureExtensionBlockingFlags
    (inputs : FeatureExtensionInputs) : Set FeatureExtensionFlag
  | .buybackFloorOk => inputs.buybackFloorOk = false
  | .buybackFloorFixedpointOk => inputs.buybackFloorFixedpointOk = false
  | .rebateOk => inputs.rebateOk = false
  | .lockWeightOk => inputs.lockWeightOk = false

@[simp] theorem mem_featureExtensionBlockingFlags
    (inputs : FeatureExtensionInputs) (flag : FeatureExtensionFlag) :
    flag ∈ featureExtensionBlockingFlags inputs ↔
      match flag with
      | .buybackFloorOk => inputs.buybackFloorOk = false
      | .buybackFloorFixedpointOk => inputs.buybackFloorFixedpointOk = false
      | .rebateOk => inputs.rebateOk = false
      | .lockWeightOk => inputs.lockWeightOk = false := Iff.rfl

theorem featureExtensionGate_eq_true_iff_no_blockers
    (inputs : FeatureExtensionInputs) :
    featureExtensionGate inputs = true ↔
      ∀ flag : FeatureExtensionFlag, flag ∉ featureExtensionBlockingFlags inputs := by
  constructor
  · intro hGate flag hBlock
    rcases (featureExtensionGate_eq_true_iff inputs).1 hGate with
      ⟨hBuyback, hFixedpoint, hRebate, hLockWeight⟩
    cases flag with
    | buybackFloorOk =>
        simp [hBuyback] at hBlock
    | buybackFloorFixedpointOk =>
        simp [hFixedpoint] at hBlock
    | rebateOk =>
        simp [hRebate] at hBlock
    | lockWeightOk =>
        simp [hLockWeight] at hBlock
  · intro hNo
    have hBuyback : inputs.buybackFloorOk = true := by
      cases hBuyback : inputs.buybackFloorOk with
      | false =>
          exfalso
          exact hNo .buybackFloorOk (by simp [hBuyback])
      | true =>
          simp
    have hFixedpoint : inputs.buybackFloorFixedpointOk = true := by
      cases hFixedpoint : inputs.buybackFloorFixedpointOk with
      | false =>
          exfalso
          exact hNo .buybackFloorFixedpointOk
            (by simp [hFixedpoint])
      | true =>
          simp
    have hRebate : inputs.rebateOk = true := by
      cases hRebate : inputs.rebateOk with
      | false =>
          exfalso
          exact hNo .rebateOk (by simp [hRebate])
      | true =>
          simp
    have hLockWeight : inputs.lockWeightOk = true := by
      cases hLockWeight : inputs.lockWeightOk with
      | false =>
          exfalso
          exact hNo .lockWeightOk (by simp [hLockWeight])
      | true =>
          simp
    exact (featureExtensionGate_eq_true_iff inputs).2
      ⟨hBuyback, hFixedpoint, hRebate, hLockWeight⟩

theorem featureExtensionGate_eq_false_iff_exists_blocker
    (inputs : FeatureExtensionInputs) :
    featureExtensionGate inputs = false ↔
      ∃ flag : FeatureExtensionFlag, flag ∈ featureExtensionBlockingFlags inputs := by
  constructor
  · intro hGate
    by_contra hNoExists
    have hNo :
        ∀ flag : FeatureExtensionFlag, flag ∉ featureExtensionBlockingFlags inputs := by
      intro flag hFlag
      exact hNoExists ⟨flag, hFlag⟩
    have hTrue := (featureExtensionGate_eq_true_iff_no_blockers inputs).2 hNo
    simp [hTrue] at hGate
  · rintro ⟨flag, hFlag⟩
    cases hGate : featureExtensionGate inputs with
    | false =>
        simp
    | true =>
        exfalso
        exact (featureExtensionGate_eq_true_iff_no_blockers inputs).1 hGate flag hFlag

def settlementEndToEndBlockingFlags
    (inputs : SettlementEndToEndInputs) : Set SettlementEndToEndGateFlag
  | .attestationMode => False
  | .strongCertificateOk => inputs.strongCertificateOk = false
  | .featureExtensionPacketOk => inputs.featureExtensionPacketOk = false
  | .moduleBundleOk => inputs.moduleBundleOk = false
  | .fullPriceRailsOk => inputs.fullPriceRailsOk = false
  | .priceProvenanceOk => inputs.priceProvenanceOk = false
  | .attestationOk =>
      inputs.attestationMode = true ∧ inputs.attestationOk = false
  | .assetConservationOk => inputs.assetConservationOk = false
  | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = false
  | .valueConservationOk => inputs.valueConservationOk = false

@[simp] theorem mem_settlementEndToEndBlockingFlags
    (inputs : SettlementEndToEndInputs) (flag : SettlementEndToEndGateFlag) :
    flag ∈ settlementEndToEndBlockingFlags inputs ↔
      match flag with
      | .attestationMode => False
      | .strongCertificateOk => inputs.strongCertificateOk = false
      | .featureExtensionPacketOk => inputs.featureExtensionPacketOk = false
      | .moduleBundleOk => inputs.moduleBundleOk = false
      | .fullPriceRailsOk => inputs.fullPriceRailsOk = false
      | .priceProvenanceOk => inputs.priceProvenanceOk = false
      | .attestationOk =>
          inputs.attestationMode = true ∧ inputs.attestationOk = false
      | .assetConservationOk => inputs.assetConservationOk = false
      | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = false
      | .valueConservationOk => inputs.valueConservationOk = false := Iff.rfl

theorem settlementEndToEndBlockingFlags_endogenousLpMode_irrelevant
    (inputs : SettlementEndToEndInputs) (flag : Bool) :
    settlementEndToEndBlockingFlags { inputs with endogenousLpMode := flag } =
      settlementEndToEndBlockingFlags inputs := by
  rfl

theorem settlementEndToEndGate_eq_true_iff_no_blockers
    (inputs : SettlementEndToEndInputs) :
    settlementEndToEndGate inputs = true ↔
      ∀ flag : SettlementEndToEndGateFlag,
        flag ∉ settlementEndToEndBlockingFlags inputs := by
  constructor
  · intro hGate flag hBlock
    rcases (settlementEndToEndGate_eq_true_iff inputs).1 hGate with
      ⟨hStrong, hFeature, hModule, hRails, hPrice, hAsset, hValue, hLiability, hAttOptional⟩
    cases flag with
    | attestationMode =>
        simp at hBlock
    | strongCertificateOk =>
        simp [hStrong] at hBlock
    | featureExtensionPacketOk =>
        simp [hFeature] at hBlock
    | moduleBundleOk =>
        simp [hModule] at hBlock
    | fullPriceRailsOk =>
        simp [hRails] at hBlock
    | priceProvenanceOk =>
        simp [hPrice] at hBlock
    | attestationOk =>
        rcases hAttOptional with hModeFalse | hAttTrue
        · simp [hModeFalse] at hBlock
        · simp [hAttTrue] at hBlock
    | assetConservationOk =>
        simp [hAsset] at hBlock
    | lpLiabilityBalancedOk =>
        simp [hLiability] at hBlock
    | valueConservationOk =>
        simp [hValue] at hBlock
  · intro hNo
    have hStrong : inputs.strongCertificateOk = true := by
      cases hStrong : inputs.strongCertificateOk with
      | false =>
          exfalso
          exact hNo .strongCertificateOk
            (by simp [hStrong])
      | true =>
          simp
    have hFeature : inputs.featureExtensionPacketOk = true := by
      cases hFeature : inputs.featureExtensionPacketOk with
      | false =>
          exfalso
          exact hNo .featureExtensionPacketOk
            (by simp [hFeature])
      | true =>
          simp
    have hModule : inputs.moduleBundleOk = true := by
      cases hModule : inputs.moduleBundleOk with
      | false =>
          exfalso
          exact hNo .moduleBundleOk
            (by simp [hModule])
      | true =>
          simp
    have hRails : inputs.fullPriceRailsOk = true := by
      cases hRails : inputs.fullPriceRailsOk with
      | false =>
          exfalso
          exact hNo .fullPriceRailsOk
            (by simp [hRails])
      | true =>
          simp
    have hPrice : inputs.priceProvenanceOk = true := by
      cases hPrice : inputs.priceProvenanceOk with
      | false =>
          exfalso
          exact hNo .priceProvenanceOk
            (by simp [hPrice])
      | true =>
          simp
    have hAsset : inputs.assetConservationOk = true := by
      cases hAsset : inputs.assetConservationOk with
      | false =>
          exfalso
          exact hNo .assetConservationOk
            (by simp [hAsset])
      | true =>
          simp
    have hValue : inputs.valueConservationOk = true := by
      cases hValue : inputs.valueConservationOk with
      | false =>
          exfalso
          exact hNo .valueConservationOk
            (by simp [hValue])
      | true =>
          simp
    have hLiability : inputs.lpLiabilityBalancedOk = true := by
      cases hLiability : inputs.lpLiabilityBalancedOk with
      | false =>
          exfalso
          exact hNo .lpLiabilityBalancedOk
            (by simp [hLiability])
      | true =>
          simp
    have hAttOptional :
        inputs.attestationMode = false ∨ inputs.attestationOk = true := by
      cases hMode : inputs.attestationMode with
      | false =>
          simp
      | true =>
          cases hAtt : inputs.attestationOk with
          | false =>
              exfalso
              exact hNo .attestationOk
                (by simp [hMode, hAtt])
          | true =>
              simp
    exact (settlementEndToEndGate_eq_true_iff inputs).2
      ⟨hStrong, hFeature, hModule, hRails, hPrice, hAsset, hValue, hLiability, hAttOptional⟩

theorem settlementEndToEndGate_eq_false_iff_exists_blocker
    (inputs : SettlementEndToEndInputs) :
    settlementEndToEndGate inputs = false ↔
      ∃ flag : SettlementEndToEndGateFlag,
        flag ∈ settlementEndToEndBlockingFlags inputs := by
  constructor
  · intro hGate
    by_contra hNoExists
    have hNo :
        ∀ flag : SettlementEndToEndGateFlag,
          flag ∉ settlementEndToEndBlockingFlags inputs := by
      intro flag hFlag
      exact hNoExists ⟨flag, hFlag⟩
    have hTrue := (settlementEndToEndGate_eq_true_iff_no_blockers inputs).2 hNo
    simp [hTrue] at hGate
  · rintro ⟨flag, hFlag⟩
    cases hGate : settlementEndToEndGate inputs with
    | false =>
        simp
    | true =>
        exfalso
        exact (settlementEndToEndGate_eq_true_iff_no_blockers inputs).1 hGate flag hFlag

end LeanMathlib
