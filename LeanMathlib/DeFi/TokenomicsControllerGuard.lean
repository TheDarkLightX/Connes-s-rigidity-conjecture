import LeanMathlib.DeFi.PostAGITokenomics
import LeanMathlib.DeFi.TokenomicsTreasuryBurn

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/--
A structural certificate for accepting dynamic tokenomics controller steps.

The controller itself can be arbitrary; this record contains only the local facts
needed to replay finite-trace safety consequences.
-/
structure TokenomicsControllerGuard
    (M : MarketSystem σ) (A S T : σ → Rat) (q : Rat) : Prop where
  supplyFactor : StepSupplyLeFactor M S q
  burnFunded : StepBurnFundedByTreasury M S T
  outputNondecreasing : StepOutputNondecreasing M A
  treasuryNonnegative : TreasuryNonnegative T
  outputNonnegative : ∀ s : σ, 0 ≤ A s
  supplyPositive : ∀ s : σ, 0 < S s

namespace TokenomicsControllerGuard

theorem stepSupplyNonincreasing
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqLeOne : q ≤ 1) :
    StepSupplyNonincreasing M S := by
  intro s t hStep
  have hFactor := hGuard.supplyFactor hStep
  have hScale : q * S s ≤ 1 * S s :=
    mul_le_mul_of_nonneg_right hqLeOne (hGuard.supplyPositive s).le
  exact hFactor.trans (by simpa using hScale)

theorem supply_le_factor_pow
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqNonneg : 0 ≤ q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ q ^ n * S s :=
  supply_le_factor_pow_of_traceN M S hqNonneg hGuard.supplyFactor hTrace

theorem supply_le_initial
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ S s :=
  supply_le_initial_of_traceN_factor
    M S hqNonneg hqLeOne hGuard.supplyFactor hTrace
    (hGuard.supplyPositive s).le

theorem traceSupplyDrop_le_initialTreasury
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceSupplyDrop S hTrace ≤ T s :=
  traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
    M S T hGuard.burnFunded hGuard.treasuryNonnegative hTrace

theorem traceSupplyDrop_between_zero_and_initialTreasury
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace ∧ traceSupplyDrop S hTrace ≤ T s :=
  _root_.LeanMathlib.DeFi.MarketSystem.traceSupplyDrop_between_zero_and_initialTreasury
    M S T (hGuard.stepSupplyNonincreasing hqLeOne)
    hGuard.burnFunded hGuard.treasuryNonnegative hTrace

theorem terminalSupply_ge_initial_minus_treasury
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S s - T s ≤ S t :=
  _root_.LeanMathlib.DeFi.MarketSystem.terminalSupply_ge_initial_minus_treasury
    M S T hGuard.burnFunded hGuard.treasuryNonnegative hTrace

theorem outputPerToken_le
    {M : MarketSystem σ} {A S T : σ → Rat} {q : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    outputPerToken A S s ≤ outputPerToken A S t :=
  outputPerToken_le_of_traceN_output_nondec_supply_factor
    M A S hqNonneg hqLeOne hGuard.outputNondecreasing
    hGuard.supplyFactor hGuard.outputNonnegative hGuard.supplyPositive hTrace

end TokenomicsControllerGuard

end MarketSystem

end DeFi

end LeanMathlib
