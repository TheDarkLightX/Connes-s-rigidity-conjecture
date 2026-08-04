import LeanMathlib.DeFi.TokenomicsControllerGuard
import LeanMathlib.DeFi.TokenomicsOracleIndexed

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/--
An oracle-indexed controller guard combines index-driven supply response with
the extra certificates needed for output-per-token and treasury safety.
-/
structure OracleIndexedControllerGuard
    (M : MarketSystem σ) (A S T I : σ → Rat) (factor : Rat → Rat) (q : Rat) :
    Prop where
  oracleGuard : OracleIndexedDeflationGuard M S I factor q
  burnFunded : StepBurnFundedByTreasury M S T
  outputNondecreasing : StepOutputNondecreasing M A
  treasuryNonnegative : TreasuryNonnegative T
  outputNonnegative : ∀ s : σ, 0 ≤ A s
  supplyPositive : ∀ s : σ, 0 < S s

namespace OracleIndexedControllerGuard

theorem toControllerGuard
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q) :
    TokenomicsControllerGuard M A S T q where
  supplyFactor := hGuard.oracleGuard.stepSupplyLeFactor
  burnFunded := hGuard.burnFunded
  outputNondecreasing := hGuard.outputNondecreasing
  treasuryNonnegative := hGuard.treasuryNonnegative
  outputNonnegative := hGuard.outputNonnegative
  supplyPositive := hGuard.supplyPositive

theorem index_le
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    I s ≤ I t :=
  hGuard.oracleGuard.index_le hTrace

theorem supply_le_factor_pow
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hqNonneg : 0 ≤ q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ q ^ n * S s :=
  hGuard.oracleGuard.supply_le_factor_pow hqNonneg hTrace

theorem traceSupplyDrop_le_initialTreasury
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceSupplyDrop S hTrace ≤ T s :=
  hGuard.toControllerGuard.traceSupplyDrop_le_initialTreasury hTrace

theorem outputPerToken_le
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    outputPerToken A S s ≤ outputPerToken A S t :=
  hGuard.toControllerGuard.outputPerToken_le hqNonneg hqLeOne hTrace

theorem index_supply_and_productivity_bounds
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    I s ≤ I t ∧
      S t ≤ q ^ n * S s ∧
      outputPerToken A S s ≤ outputPerToken A S t := by
  exact ⟨hGuard.index_le hTrace,
    hGuard.supply_le_factor_pow hqNonneg hTrace,
    hGuard.outputPerToken_le hqNonneg hqLeOne hTrace⟩

theorem index_supply_productivity_and_treasury_bounds
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    I s ≤ I t ∧
      S t ≤ q ^ n * S s ∧
      outputPerToken A S s ≤ outputPerToken A S t ∧
      traceSupplyDrop S hTrace ≤ T s := by
  exact ⟨hGuard.index_le hTrace,
    hGuard.supply_le_factor_pow hqNonneg hTrace,
    hGuard.outputPerToken_le hqNonneg hqLeOne hTrace,
    hGuard.traceSupplyDrop_le_initialTreasury hTrace⟩

end OracleIndexedControllerGuard

end MarketSystem

end DeFi

end LeanMathlib
