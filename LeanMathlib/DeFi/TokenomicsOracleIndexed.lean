import LeanMathlib.DeFi.TokenomicsSupply

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- Every step leaves the external oracle or macro index unchanged or higher. -/
def StepIndexNondecreasing (M : MarketSystem σ) (I : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → I s ≤ I t

/-- A supply response whose contraction factor is read from an index value. -/
def StepSupplyLeIndexFactor
    (M : MarketSystem σ) (S I : σ → Rat) (factor : Rat → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S t ≤ factor (I t) * S s

/-- Structural guard for index-driven deflationary supply controllers. -/
structure OracleIndexedDeflationGuard
    (M : MarketSystem σ) (S I : σ → Rat) (factor : Rat → Rat) (q : Rat) :
    Prop where
  indexNondecreasing : StepIndexNondecreasing M I
  supplyIndexFactor : StepSupplyLeIndexFactor M S I factor
  factorLe : ∀ x : Rat, factor x ≤ q
  supplyNonnegative : ∀ s : σ, 0 ≤ S s

theorem index_le_of_traceN_stepIndexNondecreasing
    (M : MarketSystem σ) (I : σ → Rat)
    (hIndex : StepIndexNondecreasing M I)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    I s ≤ I t := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact ih.trans (hIndex hStep)

namespace OracleIndexedDeflationGuard

theorem index_le
    {M : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedDeflationGuard M S I factor q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    I s ≤ I t :=
  index_le_of_traceN_stepIndexNondecreasing
    M I hGuard.indexNondecreasing hTrace

theorem stepSupplyLeFactor
    {M : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedDeflationGuard M S I factor q) :
    StepSupplyLeFactor M S q := by
  intro s t hStep
  have hStepFactor := hGuard.supplyIndexFactor hStep
  have hFactorCap : factor (I t) * S s ≤ q * S s :=
    mul_le_mul_of_nonneg_right (hGuard.factorLe (I t)) (hGuard.supplyNonnegative s)
  exact hStepFactor.trans hFactorCap

theorem supply_le_factor_pow
    {M : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedDeflationGuard M S I factor q)
    (hqNonneg : 0 ≤ q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ q ^ n * S s :=
  supply_le_factor_pow_of_traceN
    M S hqNonneg hGuard.stepSupplyLeFactor hTrace

theorem supply_le_initial
    {M : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedDeflationGuard M S I factor q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ S s :=
  supply_le_initial_of_traceN_factor
    M S hqNonneg hqLeOne hGuard.stepSupplyLeFactor hTrace
    (hGuard.supplyNonnegative s)

theorem traceSupplyDrop_nonneg
    {M : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedDeflationGuard M S I factor q)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace :=
  traceSupplyDrop_nonneg_of_traceN_factor
    M S hqNonneg hqLeOne hGuard.stepSupplyLeFactor hTrace
    (hGuard.supplyNonnegative s)

theorem index_and_supply_bounds
    {M : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hGuard : OracleIndexedDeflationGuard M S I factor q)
    (hqNonneg : 0 ≤ q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    I s ≤ I t ∧ S t ≤ q ^ n * S s :=
  ⟨hGuard.index_le hTrace,
    hGuard.supply_le_factor_pow hqNonneg hTrace⟩

end OracleIndexedDeflationGuard

end MarketSystem

end DeFi

end LeanMathlib
