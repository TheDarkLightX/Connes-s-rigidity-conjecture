import LeanMathlib.DeFi.TokenomicsSupply

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- Every step leaves the productive-output index unchanged or higher. -/
def StepOutputNondecreasing (M : MarketSystem σ) (A : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → A s ≤ A t

/-- Productive output per unit of positive circulating supply. -/
def outputPerToken (A S : σ → Rat) (s : σ) : Rat :=
  A s / S s

theorem output_le_of_traceN_stepOutputNondecreasing
    (M : MarketSystem σ) (A : σ → Rat)
    (hOutput : StepOutputNondecreasing M A)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    A s ≤ A t := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact ih.trans (hOutput hStep)

theorem outputPerToken_le_of_output_nondec_supply_noninc
    {A S : σ → Rat} {s t : σ}
    (hOutput : A s ≤ A t)
    (hOutputNonneg : 0 ≤ A s)
    (hTerminalSupplyPos : 0 < S t)
    (hSupply : S t ≤ S s) :
    outputPerToken A S s ≤ outputPerToken A S t := by
  have hInitialSupplyPos : 0 < S s :=
    hTerminalSupplyPos.trans_le hSupply
  unfold outputPerToken
  rw [div_le_div_iff₀ hInitialSupplyPos hTerminalSupplyPos]
  calc
    A s * S t ≤ A s * S s :=
      mul_le_mul_of_nonneg_left hSupply hOutputNonneg
    _ ≤ A t * S s :=
      mul_le_mul_of_nonneg_right hOutput hInitialSupplyPos.le

theorem outputPerToken_le_of_traceN_output_nondec_supply_noninc
    (M : MarketSystem σ) (A S : σ → Rat)
    (hOutput : StepOutputNondecreasing M A)
    (hSupply : StepSupplyNonincreasing M S)
    (hOutputNonneg : ∀ s : σ, 0 ≤ A s)
    (hSupplyPos : ∀ s : σ, 0 < S s)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    outputPerToken A S s ≤ outputPerToken A S t := by
  have hOutputTrace :=
    output_le_of_traceN_stepOutputNondecreasing M A hOutput hTrace
  have hSupplyTrace :=
    supply_le_of_traceN_stepSupplyNonincreasing M S hSupply hTrace
  exact outputPerToken_le_of_output_nondec_supply_noninc
    hOutputTrace (hOutputNonneg s) (hSupplyPos t) hSupplyTrace

theorem outputPerToken_le_of_traceN_output_nondec_supply_factor
    (M : MarketSystem σ) (A S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hOutput : StepOutputNondecreasing M A)
    (hFactor : StepSupplyLeFactor M S q)
    (hOutputNonneg : ∀ s : σ, 0 ≤ A s)
    (hSupplyPos : ∀ s : σ, 0 < S s)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    outputPerToken A S s ≤ outputPerToken A S t := by
  have hOutputTrace :=
    output_le_of_traceN_stepOutputNondecreasing M A hOutput hTrace
  have hSupplyTrace :=
    supply_le_initial_of_traceN_factor
      M S hqNonneg hqLeOne hFactor hTrace (hSupplyPos s).le
  exact outputPerToken_le_of_output_nondec_supply_noninc
    hOutputTrace (hOutputNonneg s) (hSupplyPos t) hSupplyTrace

end MarketSystem

end DeFi

end LeanMathlib
