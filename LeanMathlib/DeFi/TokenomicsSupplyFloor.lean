import LeanMathlib.DeFi.TokenomicsControllerGuard

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- Every one-step transition ends at or above a chosen supply floor. -/
def StepSupplyFloor (M : MarketSystem σ) (S : σ → Rat) (floor : Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → floor ≤ S t

/-- Every certified finite trace preserves a chosen supply floor. -/
def TraceSupplyFloor (M : MarketSystem σ) (S : σ → Rat) (floor : Rat) : Prop :=
  ∀ {n : Nat} {s t : σ}, TraceN M n s t → floor ≤ S s → floor ≤ S t

theorem traceSupplyFloor_of_stepSupplyFloor
    (M : MarketSystem σ) (S : σ → Rat) (floor : Rat)
    (hFloor : StepSupplyFloor M S floor) :
    TraceSupplyFloor M S floor := by
  intro n s t hTrace hInitial
  induction hTrace with
  | nil =>
      exact hInitial
  | snoc hTrace hStep ih =>
      exact hFloor hStep

theorem terminalSupply_ge_floor_of_traceN
    (M : MarketSystem σ) (S : σ → Rat) (floor : Rat)
    (hFloor : StepSupplyFloor M S floor)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitialFloor : floor ≤ S s) :
    floor ≤ S t :=
  traceSupplyFloor_of_stepSupplyFloor M S floor hFloor hTrace hInitialFloor

theorem traceSupplyDrop_le_initialMinusFloor
    {M : MarketSystem σ} (S : σ → Rat) (floor : Rat)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hTerminalFloor : floor ≤ S t) :
    traceSupplyDrop S hTrace ≤ S s - floor := by
  unfold traceSupplyDrop
  linarith

theorem supply_floor_and_initial_upper_of_factor_floor
    (M : MarketSystem σ) (S : σ → Rat) (floor : Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hFactor : StepSupplyLeFactor M S q)
    (hFloor : StepSupplyFloor M S floor)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    floor ≤ S t ∧ S t ≤ S s := by
  have hInitialNonneg : 0 ≤ S s := hFloorNonneg.trans hInitialFloor
  exact
    ⟨terminalSupply_ge_floor_of_traceN M S floor hFloor hTrace hInitialFloor,
      supply_le_initial_of_traceN_factor
        M S hqNonneg hqLeOne hFactor hTrace hInitialNonneg⟩

theorem traceSupplyDrop_between_zero_and_initialMinusFloor_of_factor_floor
    (M : MarketSystem σ) (S : σ → Rat) (floor : Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hFactor : StepSupplyLeFactor M S q)
    (hFloor : StepSupplyFloor M S floor)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    0 ≤ traceSupplyDrop S hTrace ∧ traceSupplyDrop S hTrace ≤ S s - floor := by
  have hBounds :=
    supply_floor_and_initial_upper_of_factor_floor
      M S floor hqNonneg hqLeOne hFactor hFloor hTrace
      hFloorNonneg hInitialFloor
  exact
    ⟨by
      unfold traceSupplyDrop
      exact sub_nonneg.mpr hBounds.2,
    traceSupplyDrop_le_initialMinusFloor S floor hTrace hBounds.1⟩

theorem controller_supply_floor_and_initial_upper
    {M : MarketSystem σ} {A S T : σ → Rat} {q floor : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    floor ≤ S t ∧ S t ≤ S s :=
  supply_floor_and_initial_upper_of_factor_floor
    M S floor hqNonneg hqLeOne hGuard.supplyFactor hFloor hTrace
    hFloorNonneg hInitialFloor

theorem controller_traceSupplyDrop_between_zero_and_initialMinusFloor
    {M : MarketSystem σ} {A S T : σ → Rat} {q floor : Rat}
    (hGuard : TokenomicsControllerGuard M A S T q)
    (hFloor : StepSupplyFloor M S floor)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hFloorNonneg : 0 ≤ floor)
    (hInitialFloor : floor ≤ S s) :
    0 ≤ traceSupplyDrop S hTrace ∧ traceSupplyDrop S hTrace ≤ S s - floor :=
  traceSupplyDrop_between_zero_and_initialMinusFloor_of_factor_floor
    M S floor hqNonneg hqLeOne hGuard.supplyFactor hFloor hTrace
    hFloorNonneg hInitialFloor

end MarketSystem

end DeFi

end LeanMathlib
