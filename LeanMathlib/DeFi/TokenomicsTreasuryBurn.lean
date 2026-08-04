import LeanMathlib.DeFi.TokenomicsSupply

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- Every one-step supply burn is funded by a treasury or resource-account drawdown. -/
def StepBurnFundedByTreasury
    (M : MarketSystem σ) (S T : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S s - S t ≤ T s - T t

/-- The treasury or resource account is nonnegative at every state. -/
def TreasuryNonnegative (T : σ → Rat) : Prop :=
  ∀ s : σ, 0 ≤ T s

theorem traceSupplyDrop_le_treasuryDrop_of_stepBurnFunded
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceSupplyDrop S hTrace ≤ T s - T t := by
  induction hTrace with
  | nil =>
      simp [traceSupplyDrop]
  | snoc hTrace hStep ih =>
      have hStepFunded := hFunded hStep
      unfold traceSupplyDrop at ih hStepFunded ⊢
      linarith

theorem traceSupplyDrop_le_initialTreasury_of_stepBurnFunded
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hTerminalTreasury : 0 ≤ T t) :
    traceSupplyDrop S hTrace ≤ T s := by
  have hDrop :=
    traceSupplyDrop_le_treasuryDrop_of_stepBurnFunded
      M S T hFunded hTrace
  unfold traceSupplyDrop at hDrop ⊢
  linarith

theorem traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceSupplyDrop S hTrace ≤ T s :=
  traceSupplyDrop_le_initialTreasury_of_stepBurnFunded
    M S T hFunded hTrace (hTreasury t)

theorem traceSupplyDrop_between_zero_and_initialTreasury
    (M : MarketSystem σ) (S T : σ → Rat)
    (hSupply : StepSupplyNonincreasing M S)
    (hFunded : StepBurnFundedByTreasury M S T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace ∧ traceSupplyDrop S hTrace ≤ T s :=
  ⟨traceSupplyDrop_nonneg_of_stepSupplyNonincreasing M S hSupply hTrace,
    traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
      M S T hFunded hTreasury hTrace⟩

theorem terminalSupply_ge_initial_minus_treasury
    (M : MarketSystem σ) (S T : σ → Rat)
    (hFunded : StepBurnFundedByTreasury M S T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S s - T s ≤ S t := by
  have hDrop :=
    traceSupplyDrop_le_initialTreasury_of_stepBurnFunded_nonnegativeTreasury
      M S T hFunded hTreasury hTrace
  unfold traceSupplyDrop at hDrop
  linarith

end MarketSystem

end DeFi

end LeanMathlib
