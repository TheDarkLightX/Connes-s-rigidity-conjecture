import LeanMathlib.DeFi.TokenomicsOracleController
import LeanMathlib.DeFi.TokenomicsSupplyFloor

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

theorem controller_trace_safety_envelope
    {M : MarketSystem σ} {A S T : σ → Rat} {q floor : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    floor ≤ S t ∧
      S t ≤ S s ∧
      0 ≤ traceSupplyDrop S hTrace ∧
      traceSupplyDrop S hTrace ≤ S s - floor ∧
      traceSupplyDrop S hTrace ≤ T s ∧
      outputPerToken A S s ≤ outputPerToken A S t := by
  have hSupplyBounds :=
    controller_supply_floor_and_initial_upper
      hGuard hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  have hDropFloor :=
    controller_traceSupplyDrop_between_zero_and_initialMinusFloor
      hGuard hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  have hDropTreasury :=
    hGuard.traceSupplyDrop_le_initialTreasury hTrace
  have hProductivity :=
    hGuard.outputPerToken_le hqNonneg hqLeOne hTrace
  exact ⟨hSupplyBounds.1,
    hSupplyBounds.2,
    hDropFloor.1,
    hDropFloor.2,
    hDropTreasury,
    hProductivity⟩

theorem oracle_controller_trace_safety_envelope
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat}
    {q floor : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    I s ≤ I t ∧
      floor ≤ S t ∧
      S t ≤ S s ∧
      0 ≤ traceSupplyDrop S hTrace ∧
      traceSupplyDrop S hTrace ≤ S s - floor ∧
      traceSupplyDrop S hTrace ≤ T s ∧
      outputPerToken A S s ≤ outputPerToken A S t := by
  have hController := hGuard.toControllerGuard
  have hEnvelope :=
    controller_trace_safety_envelope
      hController hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  exact ⟨hGuard.index_le hTrace,
    hEnvelope.1,
    hEnvelope.2.1,
    hEnvelope.2.2.1,
    hEnvelope.2.2.2.1,
    hEnvelope.2.2.2.2.1,
    hEnvelope.2.2.2.2.2⟩

theorem oracle_controller_geometric_safety_envelope
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat}
    {q floor : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    I s ≤ I t ∧
      floor ≤ S t ∧
      S t ≤ q ^ n * S s ∧
      traceSupplyDrop S hTrace ≤ S s - floor ∧
      traceSupplyDrop S hTrace ≤ T s ∧
      outputPerToken A S s ≤ outputPerToken A S t := by
  have hSupplyPow := hGuard.supply_le_factor_pow hqNonneg hTrace
  have hEnvelope :=
    oracle_controller_trace_safety_envelope
      hGuard hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  exact ⟨hEnvelope.1,
    hEnvelope.2.1,
    hSupplyPow,
    hEnvelope.2.2.2.2.1,
    hEnvelope.2.2.2.2.2.1,
    hEnvelope.2.2.2.2.2.2⟩

end MarketSystem

end DeFi

end LeanMathlib
