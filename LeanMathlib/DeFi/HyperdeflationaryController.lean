import LeanMathlib.DeFi.TokenomicsSafetyEnvelope
import LeanMathlib.DeFi.TokenomicsSafetyComposition

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ τ : Type*}

theorem hyperdeflationary_no_ruin_envelope
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
      0 ≤ T t ∧
      S t ≤ q ^ n * S s ∧
      traceSupplyDrop S hTrace ≤ S s - floor ∧
      traceSupplyDrop S hTrace ≤ T s ∧
      outputPerToken A S s ≤ outputPerToken A S t := by
  have hEnvelope :=
    oracle_controller_geometric_safety_envelope
      hGuard hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  exact ⟨hEnvelope.1,
    hEnvelope.2.1,
    hGuard.treasuryNonnegative t,
    hEnvelope.2.2.1,
    hEnvelope.2.2.2.1,
    hEnvelope.2.2.2.2.1,
    hEnvelope.2.2.2.2.2⟩

theorem hyperdeflationary_terminal_supply_nonnegative
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat}
    {q floor : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    0 ≤ S t ∧ 0 ≤ T t := by
  have hEnvelope :=
    hyperdeflationary_no_ruin_envelope
      hGuard hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  exact ⟨hFloorNonneg.trans hEnvelope.2.1, hEnvelope.2.2.1⟩

theorem hyperdeflationary_terminal_supply_positive
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat}
    {q floor : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorPositive : 0 < floor)
    (hInitialFloor : floor ≤ S s) :
    0 < S t := by
  have hEnvelope :=
    hyperdeflationary_no_ruin_envelope
      hGuard hFloor hqNonneg hqLeOne hTrace
      (le_of_lt hFloorPositive) hInitialFloor
  exact hFloorPositive.trans_le hEnvelope.2.1

theorem hyperdeflationary_traceSupplyDrop_le_initialSupply
    {M : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat}
    {q floor : Rat}
    (hGuard : OracleIndexedControllerGuard M A S T I factor q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    traceSupplyDrop S hTrace ≤ S s := by
  have hEnvelope :=
    hyperdeflationary_no_ruin_envelope
      hGuard hFloor hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor
  linarith [hEnvelope.2.2.2.2.1]

theorem stepSupplyFloor_of_stepIncluded
    {M N : MarketSystem σ} {S : σ → Rat} {floor : Rat}
    (hInc : StepIncluded M N)
    (hFloor : StepSupplyFloor N S floor) :
    StepSupplyFloor M S floor := by
  intro s t hStep
  exact hFloor (hInc hStep)

theorem oracleIndexedDeflationGuard_of_stepIncluded
    {M N : MarketSystem σ} {S I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hInc : StepIncluded M N)
    (hGuard : OracleIndexedDeflationGuard N S I factor q) :
    OracleIndexedDeflationGuard M S I factor q where
  indexNondecreasing := by
    intro s t hStep
    exact hGuard.indexNondecreasing (hInc hStep)
  supplyIndexFactor := by
    intro s t hStep
    exact hGuard.supplyIndexFactor (hInc hStep)
  factorLe := hGuard.factorLe
  supplyNonnegative := hGuard.supplyNonnegative

theorem oracleIndexedControllerGuard_of_stepIncluded
    {M N : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat} {q : Rat}
    (hInc : StepIncluded M N)
    (hGuard : OracleIndexedControllerGuard N A S T I factor q) :
    OracleIndexedControllerGuard M A S T I factor q where
  oracleGuard :=
    oracleIndexedDeflationGuard_of_stepIncluded hInc hGuard.oracleGuard
  burnFunded := by
    intro s t hStep
    exact hGuard.burnFunded (hInc hStep)
  outputNondecreasing := by
    intro s t hStep
    exact hGuard.outputNondecreasing (hInc hStep)
  treasuryNonnegative := hGuard.treasuryNonnegative
  outputNonnegative := hGuard.outputNonnegative
  supplyPositive := hGuard.supplyPositive

theorem hyperdeflationary_no_ruin_envelope_of_stepIncluded
    {M N : MarketSystem σ} {A S T I : σ → Rat} {factor : Rat → Rat}
    {q floor : Rat}
    (hInc : StepIncluded M N)
    (hGuard : OracleIndexedControllerGuard N A S T I factor q)
    (hFloor : StepSupplyFloor N S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    I s ≤ I t ∧
      floor ≤ S t ∧
      0 ≤ T t ∧
      S t ≤ q ^ n * S s ∧
      traceSupplyDrop S hTrace ≤ S s - floor ∧
      traceSupplyDrop S hTrace ≤ T s ∧
      outputPerToken A S s ≤ outputPerToken A S t :=
  hyperdeflationary_no_ruin_envelope
    (oracleIndexedControllerGuard_of_stepIncluded hInc hGuard)
    (stepSupplyFloor_of_stepIncluded hInc hFloor)
    hqNonneg hqLeOne hTrace hFloorNonneg hInitialFloor

theorem syncProduct_hyperdeflationary_trace_safety_envelope_add
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {A₁ S₁ T₁ I₁ : σ → Rat} {A₂ S₂ T₂ I₂ : τ → Rat}
    {factor₁ factor₂ : Rat → Rat} {q floor₁ floor₂ : Rat}
    (hGuard₁ : OracleIndexedControllerGuard M₁ A₁ S₁ T₁ I₁ factor₁ q)
    (hGuard₂ : OracleIndexedControllerGuard M₂ A₂ S₂ T₂ I₂ factor₂ q)
    (hFloor₁ : StepSupplyFloor M₁ S₁ floor₁)
    (hFloor₂ : StepSupplyFloor M₂ S₂ floor₂)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ × τ}
    (hTrace : TraceN (syncProduct M₁ M₂) n s t)
    (hFloor₁Nonneg : 0 ≤ floor₁)
    (hFloor₂Nonneg : 0 ≤ floor₂)
    (hInitialFloor : floor₁ + floor₂ ≤ S₁ s.1 + S₂ s.2) :
    floor₁ + floor₂ ≤ S₁ t.1 + S₂ t.2 ∧
      S₁ t.1 + S₂ t.2 ≤ S₁ s.1 + S₂ s.2 ∧
      0 ≤ T₁ t.1 + T₂ t.2 ∧
      0 ≤ traceSupplyDrop
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ∧
      traceSupplyDrop
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ≤
          (S₁ s.1 + S₂ s.2) - (floor₁ + floor₂) ∧
      traceSupplyDrop
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ≤
          T₁ s.1 + T₂ s.2 ∧
      outputPerToken
        (fun x : σ × τ => A₁ x.1 + A₂ x.2)
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) s ≤
      outputPerToken
        (fun x : σ × τ => A₁ x.1 + A₂ x.2)
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) t := by
  have hEnvelope :=
    syncProduct_controller_trace_safety_envelope_add
      hGuard₁.toControllerGuard hGuard₂.toControllerGuard
      hFloor₁ hFloor₂ hqNonneg hqLeOne hTrace
      hFloor₁Nonneg hFloor₂Nonneg hInitialFloor
  exact ⟨hEnvelope.1,
    hEnvelope.2.1,
    add_nonneg
      (hGuard₁.treasuryNonnegative t.1)
      (hGuard₂.treasuryNonnegative t.2),
    hEnvelope.2.2.1,
    hEnvelope.2.2.2.1,
    hEnvelope.2.2.2.2.1,
    hEnvelope.2.2.2.2.2⟩

end MarketSystem

end DeFi

end LeanMathlib
