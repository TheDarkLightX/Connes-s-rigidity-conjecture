import LeanMathlib.ZenoDEX.SettlementEndogenousLPValuePacket

namespace LeanMathlib

def toProjectedSettlementValueInputs
    (inputs : SettlementEndogenousLPValueInputs) : SettlementValueInputs :=
  {
    lpMode := true
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
  }

@[simp] theorem settlementEndogenousLPValueGate_eq_extra_and_projectedBase
    (inputs : SettlementEndogenousLPValueInputs) :
    settlementEndogenousLPValueGate inputs =
      (inputs.uniquePoolIdsOk &&
        inputs.allPositiveLpSupplyOk &&
        inputs.allAssetsPricedOk &&
        settlementValueGate (toProjectedSettlementValueInputs inputs)) := by
  simp [settlementEndogenousLPValueGate, settlementValueGate,
    toProjectedSettlementValueInputs, optionalGate,
    Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem settlementEndogenousLPValueGate_eq_true_iff_extra_and_projectedBase
    (inputs : SettlementEndogenousLPValueInputs) :
    settlementEndogenousLPValueGate inputs = true ↔
      inputs.uniquePoolIdsOk = true ∧
      inputs.allPositiveLpSupplyOk = true ∧
      inputs.allAssetsPricedOk = true ∧
      settlementValueGate (toProjectedSettlementValueInputs inputs) = true := by
  simp [settlementEndogenousLPValueGate_eq_extra_and_projectedBase, and_assoc]

theorem settlementEndogenousLPValueGate_true_implies_projectedBase
    {inputs : SettlementEndogenousLPValueInputs}
    (hGate : settlementEndogenousLPValueGate inputs = true) :
    settlementValueGate (toProjectedSettlementValueInputs inputs) = true := by
  exact (settlementEndogenousLPValueGate_eq_true_iff_extra_and_projectedBase inputs).1 hGate |>.2.2.2

theorem settlementEndogenousLPValueGate_eq_false_iff_extra_failure_or_base_blocker
    (inputs : SettlementEndogenousLPValueInputs) :
    settlementEndogenousLPValueGate inputs = false ↔
      inputs.uniquePoolIdsOk = false ∨
      inputs.allPositiveLpSupplyOk = false ∨
      inputs.allAssetsPricedOk = false ∨
      ∃ flag : SettlementValueFlag,
        flag ∈ settlementValueBlockingFlags (toProjectedSettlementValueInputs inputs) := by
  rw [settlementEndogenousLPValueGate_eq_extra_and_projectedBase]
  constructor
  · intro hGate
    have h :
        inputs.uniquePoolIdsOk = false ∨
          inputs.allPositiveLpSupplyOk = false ∨
          inputs.allAssetsPricedOk = false ∨
          settlementValueGate (toProjectedSettlementValueInputs inputs) = false := by
      cases hUnique : inputs.uniquePoolIdsOk <;>
        cases hPositive : inputs.allPositiveLpSupplyOk <;>
        cases hPriced : inputs.allAssetsPricedOk <;>
        cases hBase : settlementValueGate (toProjectedSettlementValueInputs inputs) <;>
        simp [hUnique, hPositive, hPriced, hBase] at hGate ⊢
    rcases h with hUnique | hRest
    · exact Or.inl hUnique
    · rcases hRest with hPositive | hRest
      · exact Or.inr <| Or.inl hPositive
      · rcases hRest with hPriced | hBase
        · exact Or.inr <| Or.inr <| Or.inl hPriced
        · exact Or.inr <| Or.inr <| Or.inr <|
            (settlementValueGate_eq_false_iff_exists_blocker
              (inputs := toProjectedSettlementValueInputs inputs)).1 hBase
  · intro h
    rcases h with hUnique | hRest
    · simp [hUnique]
    · rcases hRest with hPositive | hRest
      · simp [hPositive]
      · rcases hRest with hPriced | hBase
        · simp [hPriced]
        · have hProjected :
            settlementValueGate (toProjectedSettlementValueInputs inputs) = false :=
            (settlementValueGate_eq_false_iff_exists_blocker
              (inputs := toProjectedSettlementValueInputs inputs)).2 hBase
          simp [hProjected]

namespace UpstreamMirror
namespace TauSwap
namespace SettlementEndogenousLPValuePacket

@[simp] theorem buildPacket_packetOk_eq_extra_and_projectedBase
    (inputs : Inputs) :
    (buildPacket inputs).packetOk =
      (inputs.uniquePoolIdsOk &&
        inputs.allPositiveLpSupplyOk &&
        inputs.allAssetsPricedOk &&
        settlementValueGate
          (toProjectedSettlementValueInputs (toCurated inputs))) := by
  calc
    (buildPacket inputs).packetOk
      = settlementEndogenousLPValueGate (toCurated inputs) := by
          rfl
    _ = (inputs.uniquePoolIdsOk &&
          inputs.allPositiveLpSupplyOk &&
          inputs.allAssetsPricedOk &&
          settlementValueGate
            (toProjectedSettlementValueInputs (toCurated inputs))) :=
          settlementEndogenousLPValueGate_eq_extra_and_projectedBase
            (inputs := toCurated inputs)

theorem buildPacket_packetOk_eq_false_iff_extra_failure_or_base_blocker
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔
      inputs.uniquePoolIdsOk = false ∨
      inputs.allPositiveLpSupplyOk = false ∨
      inputs.allAssetsPricedOk = false ∨
      ∃ flag : SettlementValueFlag,
        flag ∈ settlementValueBlockingFlags
          (toProjectedSettlementValueInputs (toCurated inputs)) := by
  simpa using
    (settlementEndogenousLPValueGate_eq_false_iff_extra_failure_or_base_blocker
      (inputs := toCurated inputs))

end SettlementEndogenousLPValuePacket
end TauSwap
end UpstreamMirror

end LeanMathlib
