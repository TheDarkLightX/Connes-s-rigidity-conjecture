import LeanMathlib.PacketGateBlockers

namespace LeanMathlib

open scoped symmDiff

structure SettlementEndogenousLPValueInputs where
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  uniquePoolIdsOk : Bool
  allPositiveLpSupplyOk : Bool
  allAssetsPricedOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

def settlementEndogenousLPValueGate
    (inputs : SettlementEndogenousLPValueInputs) : Bool :=
  inputs.priceProvenanceOk &&
    inputs.uniquePoolIdsOk &&
    inputs.allPositiveLpSupplyOk &&
    inputs.allAssetsPricedOk &&
    inputs.assetConservationOk &&
    inputs.lpLiabilityBalancedOk &&
    inputs.valueConservationOk &&
    optionalGate inputs.attestationMode inputs.attestationOk

theorem settlementEndogenousLPValueGate_eq_true_iff
    (inputs : SettlementEndogenousLPValueInputs) :
    settlementEndogenousLPValueGate inputs = true ↔
      inputs.priceProvenanceOk = true ∧
      inputs.uniquePoolIdsOk = true ∧
      inputs.allPositiveLpSupplyOk = true ∧
      inputs.allAssetsPricedOk = true ∧
      inputs.assetConservationOk = true ∧
      inputs.lpLiabilityBalancedOk = true ∧
      inputs.valueConservationOk = true ∧
      (inputs.attestationMode = false ∨ inputs.attestationOk = true) := by
  simp [settlementEndogenousLPValueGate, optionalGate, and_assoc]

inductive SettlementEndogenousLPValueFlag
  | attestationMode
  | priceProvenanceOk
  | attestationOk
  | uniquePoolIdsOk
  | allPositiveLpSupplyOk
  | allAssetsPricedOk
  | assetConservationOk
  | lpLiabilityBalancedOk
  | valueConservationOk
  deriving DecidableEq, Fintype, Repr

def activeSettlementEndogenousLPValueFlags
    (inputs : SettlementEndogenousLPValueInputs) :
    Set SettlementEndogenousLPValueFlag
  | .attestationMode => inputs.attestationMode = true
  | .priceProvenanceOk => inputs.priceProvenanceOk = true
  | .attestationOk => inputs.attestationOk = true
  | .uniquePoolIdsOk => inputs.uniquePoolIdsOk = true
  | .allPositiveLpSupplyOk => inputs.allPositiveLpSupplyOk = true
  | .allAssetsPricedOk => inputs.allAssetsPricedOk = true
  | .assetConservationOk => inputs.assetConservationOk = true
  | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = true
  | .valueConservationOk => inputs.valueConservationOk = true

@[simp] theorem mem_activeSettlementEndogenousLPValueFlags
    (inputs : SettlementEndogenousLPValueInputs)
    (flag : SettlementEndogenousLPValueFlag) :
    flag ∈ activeSettlementEndogenousLPValueFlags inputs ↔
      match flag with
      | .attestationMode => inputs.attestationMode = true
      | .priceProvenanceOk => inputs.priceProvenanceOk = true
      | .attestationOk => inputs.attestationOk = true
      | .uniquePoolIdsOk => inputs.uniquePoolIdsOk = true
      | .allPositiveLpSupplyOk => inputs.allPositiveLpSupplyOk = true
      | .allAssetsPricedOk => inputs.allAssetsPricedOk = true
      | .assetConservationOk => inputs.assetConservationOk = true
      | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = true
      | .valueConservationOk => inputs.valueConservationOk = true := Iff.rfl

theorem settlementEndogenousLPValueGate_eq_of_activeFlags_eq
    {x y : SettlementEndogenousLPValueInputs}
    (hxy :
      activeSettlementEndogenousLPValueFlags x =
        activeSettlementEndogenousLPValueFlags y) :
    settlementEndogenousLPValueGate x = settlementEndogenousLPValueGate y := by
  have hAttestationMode : x.attestationMode = y.attestationMode := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.attestationMode ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hPrice : x.priceProvenanceOk = y.priceProvenanceOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.priceProvenanceOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hAttestation : x.attestationOk = y.attestationOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.attestationOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hUniquePools : x.uniquePoolIdsOk = y.uniquePoolIdsOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.uniquePoolIdsOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hPositiveSupply : x.allPositiveLpSupplyOk = y.allPositiveLpSupplyOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.allPositiveLpSupplyOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hAllAssetsPriced : x.allAssetsPricedOk = y.allAssetsPricedOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.allAssetsPricedOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hAsset : x.assetConservationOk = y.assetConservationOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.assetConservationOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hLiability : x.lpLiabilityBalancedOk = y.lpLiabilityBalancedOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.lpLiabilityBalancedOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  have hValue : x.valueConservationOk = y.valueConservationOk := by
    have := congrArg
      (fun s : Set SettlementEndogenousLPValueFlag =>
        SettlementEndogenousLPValueFlag.valueConservationOk ∈ s) hxy
    simpa [activeSettlementEndogenousLPValueFlags] using this
  simp [settlementEndogenousLPValueGate, optionalGate, hAttestationMode, hPrice,
    hAttestation, hUniquePools, hPositiveSupply, hAllAssetsPriced, hAsset,
    hLiability, hValue]

theorem activeSettlementEndogenousLPValueFlags_ne_iff_exists_mem_symmDiff
    (x y : SettlementEndogenousLPValueInputs) :
    activeSettlementEndogenousLPValueFlags x ≠
        activeSettlementEndogenousLPValueFlags y ↔
      ∃ flag : SettlementEndogenousLPValueFlag,
        flag ∈ activeSettlementEndogenousLPValueFlags x ∆
          activeSettlementEndogenousLPValueFlags y := by
  simpa using
    (set_ne_iff_exists_mem_symmDiff
      (s := activeSettlementEndogenousLPValueFlags x)
      (t := activeSettlementEndogenousLPValueFlags y))

theorem exists_endogenousLPValue_flag_witness_of_gate_ne
    {x y : SettlementEndogenousLPValueInputs}
    (hxy : settlementEndogenousLPValueGate x ≠ settlementEndogenousLPValueGate y) :
    ∃ flag : SettlementEndogenousLPValueFlag,
      flag ∈ activeSettlementEndogenousLPValueFlags x ∆
        activeSettlementEndogenousLPValueFlags y := by
  have hset :
      activeSettlementEndogenousLPValueFlags x ≠
        activeSettlementEndogenousLPValueFlags y := by
    intro hEq
    exact hxy (settlementEndogenousLPValueGate_eq_of_activeFlags_eq hEq)
  exact
    (activeSettlementEndogenousLPValueFlags_ne_iff_exists_mem_symmDiff x y).1 hset

def settlementEndogenousLPValueBlockingFlags
    (inputs : SettlementEndogenousLPValueInputs) :
    Set SettlementEndogenousLPValueFlag
  | .attestationMode => False
  | .priceProvenanceOk => inputs.priceProvenanceOk = false
  | .attestationOk => inputs.attestationMode = true ∧ inputs.attestationOk = false
  | .uniquePoolIdsOk => inputs.uniquePoolIdsOk = false
  | .allPositiveLpSupplyOk => inputs.allPositiveLpSupplyOk = false
  | .allAssetsPricedOk => inputs.allAssetsPricedOk = false
  | .assetConservationOk => inputs.assetConservationOk = false
  | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = false
  | .valueConservationOk => inputs.valueConservationOk = false

@[simp] theorem mem_settlementEndogenousLPValueBlockingFlags
    (inputs : SettlementEndogenousLPValueInputs)
    (flag : SettlementEndogenousLPValueFlag) :
    flag ∈ settlementEndogenousLPValueBlockingFlags inputs ↔
      match flag with
      | .attestationMode => False
      | .priceProvenanceOk => inputs.priceProvenanceOk = false
      | .attestationOk =>
          inputs.attestationMode = true ∧ inputs.attestationOk = false
      | .uniquePoolIdsOk => inputs.uniquePoolIdsOk = false
      | .allPositiveLpSupplyOk => inputs.allPositiveLpSupplyOk = false
      | .allAssetsPricedOk => inputs.allAssetsPricedOk = false
      | .assetConservationOk => inputs.assetConservationOk = false
      | .lpLiabilityBalancedOk => inputs.lpLiabilityBalancedOk = false
      | .valueConservationOk => inputs.valueConservationOk = false := Iff.rfl

theorem settlementEndogenousLPValueGate_eq_true_iff_no_blockers
    (inputs : SettlementEndogenousLPValueInputs) :
    settlementEndogenousLPValueGate inputs = true ↔
      ∀ flag : SettlementEndogenousLPValueFlag,
        flag ∉ settlementEndogenousLPValueBlockingFlags inputs := by
  constructor
  · intro hGate flag hBlock
    rcases (settlementEndogenousLPValueGate_eq_true_iff inputs).1 hGate with
      ⟨hPrice, hUniquePools, hPositiveSupply, hAllAssetsPriced, hAsset,
        hLiability, hValue, hAttOptional⟩
    cases flag with
    | attestationMode =>
        simp at hBlock
    | priceProvenanceOk =>
        simp [hPrice] at hBlock
    | attestationOk =>
        rcases hAttOptional with hModeFalse | hAttTrue
        · simp [hModeFalse] at hBlock
        · simp [hAttTrue] at hBlock
    | uniquePoolIdsOk =>
        simp [hUniquePools] at hBlock
    | allPositiveLpSupplyOk =>
        simp [hPositiveSupply] at hBlock
    | allAssetsPricedOk =>
        simp [hAllAssetsPriced] at hBlock
    | assetConservationOk =>
        simp [hAsset] at hBlock
    | lpLiabilityBalancedOk =>
        simp [hLiability] at hBlock
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
    have hUniquePools : inputs.uniquePoolIdsOk = true := by
      cases hUniquePools : inputs.uniquePoolIdsOk with
      | false =>
          exfalso
          exact hNo .uniquePoolIdsOk (by simp [hUniquePools])
      | true =>
          simp
    have hPositiveSupply : inputs.allPositiveLpSupplyOk = true := by
      cases hPositiveSupply : inputs.allPositiveLpSupplyOk with
      | false =>
          exfalso
          exact hNo .allPositiveLpSupplyOk (by simp [hPositiveSupply])
      | true =>
          simp
    have hAllAssetsPriced : inputs.allAssetsPricedOk = true := by
      cases hAllAssetsPriced : inputs.allAssetsPricedOk with
      | false =>
          exfalso
          exact hNo .allAssetsPricedOk (by simp [hAllAssetsPriced])
      | true =>
          simp
    have hAsset : inputs.assetConservationOk = true := by
      cases hAsset : inputs.assetConservationOk with
      | false =>
          exfalso
          exact hNo .assetConservationOk (by simp [hAsset])
      | true =>
          simp
    have hLiability : inputs.lpLiabilityBalancedOk = true := by
      cases hLiability : inputs.lpLiabilityBalancedOk with
      | false =>
          exfalso
          exact hNo .lpLiabilityBalancedOk (by simp [hLiability])
      | true =>
          simp
    have hValue : inputs.valueConservationOk = true := by
      cases hValue : inputs.valueConservationOk with
      | false =>
          exfalso
          exact hNo .valueConservationOk (by simp [hValue])
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
              exact hNo .attestationOk (by simp [hMode, hAtt])
          | true =>
              simp
    exact (settlementEndogenousLPValueGate_eq_true_iff inputs).2
      ⟨hPrice, hUniquePools, hPositiveSupply, hAllAssetsPriced, hAsset,
        hLiability, hValue, hAttOptional⟩

theorem settlementEndogenousLPValueGate_eq_false_iff_exists_blocker
    (inputs : SettlementEndogenousLPValueInputs) :
    settlementEndogenousLPValueGate inputs = false ↔
      ∃ flag : SettlementEndogenousLPValueFlag,
        flag ∈ settlementEndogenousLPValueBlockingFlags inputs := by
  constructor
  · intro hGate
    by_contra hNoExists
    have hNo :
        ∀ flag : SettlementEndogenousLPValueFlag,
          flag ∉ settlementEndogenousLPValueBlockingFlags inputs := by
      intro flag hFlag
      exact hNoExists ⟨flag, hFlag⟩
    have hTrue := (settlementEndogenousLPValueGate_eq_true_iff_no_blockers inputs).2 hNo
    simp [hTrue] at hGate
  · rintro ⟨flag, hFlag⟩
    cases hGate : settlementEndogenousLPValueGate inputs with
    | false =>
        simp
    | true =>
        exfalso
        exact (settlementEndogenousLPValueGate_eq_true_iff_no_blockers inputs).1
          hGate flag hFlag

namespace UpstreamMirror
namespace TauSwap
namespace SettlementEndogenousLPValuePacket

structure Inputs where
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  uniquePoolIdsOk : Bool
  allPositiveLpSupplyOk : Bool
  allAssetsPricedOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  uniquePoolIdsOk : Bool
  allPositiveLpSupplyOk : Bool
  allAssetsPricedOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    uniquePoolIdsOk := inputs.uniquePoolIdsOk
    allPositiveLpSupplyOk := inputs.allPositiveLpSupplyOk
    allAssetsPricedOk := inputs.allAssetsPricedOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
    packetOk :=
      inputs.priceProvenanceOk &&
      inputs.uniquePoolIdsOk &&
      inputs.allPositiveLpSupplyOk &&
      inputs.allAssetsPricedOk &&
      inputs.assetConservationOk &&
      inputs.lpLiabilityBalancedOk &&
      inputs.valueConservationOk &&
      (if inputs.attestationMode then inputs.attestationOk else true)
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

theorem verifyPacket_of_build (inputs : Inputs) :
    verifyPacket inputs (buildPacket inputs) := by
  rfl

theorem verifyingPacket_unique (inputs : Inputs) {packet : Packet}
    (hVerify : verifyPacket inputs packet) :
    packet = buildPacket inputs := by
  exact hVerify

def toCurated (inputs : Inputs) : SettlementEndogenousLPValueInputs :=
  {
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    uniquePoolIdsOk := inputs.uniquePoolIdsOk
    allPositiveLpSupplyOk := inputs.allPositiveLpSupplyOk
    allAssetsPricedOk := inputs.allAssetsPricedOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
  }

@[simp] theorem buildPacket_packetOk_eq_curatedGate (inputs : Inputs) :
    (buildPacket inputs).packetOk =
      settlementEndogenousLPValueGate (toCurated inputs) := by
  rfl

@[simp] theorem buildPacket_packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      ∀ flag : SettlementEndogenousLPValueFlag,
        flag ∉ settlementEndogenousLPValueBlockingFlags (toCurated inputs) := by
  simpa using
    (settlementEndogenousLPValueGate_eq_true_iff_no_blockers
      (inputs := toCurated inputs))

@[simp] theorem buildPacket_packetOk_eq_false_iff_exists_blocker
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔
      ∃ flag : SettlementEndogenousLPValueFlag,
        flag ∈ settlementEndogenousLPValueBlockingFlags (toCurated inputs) := by
  simpa using
    (settlementEndogenousLPValueGate_eq_false_iff_exists_blocker
      (inputs := toCurated inputs))

theorem exists_flag_witness_of_packetOk_ne {x y : Inputs}
    (hxy : (buildPacket x).packetOk ≠ (buildPacket y).packetOk) :
    ∃ flag : SettlementEndogenousLPValueFlag,
      flag ∈ activeSettlementEndogenousLPValueFlags (toCurated x) ∆
        activeSettlementEndogenousLPValueFlags (toCurated y) := by
  exact exists_endogenousLPValue_flag_witness_of_gate_ne <|
    by simpa using hxy

end SettlementEndogenousLPValuePacket
end TauSwap
end UpstreamMirror

end LeanMathlib
