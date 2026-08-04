import LeanMathlib.DeFi.TraceValueBounds

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- Each one-step value gain is bounded by the drop in a potential account. -/
def StepValueBoundedByPotential
    (M : MarketSystem σ) (V P : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → V t - V s ≤ P s - P t

/-- The potential account is nondecreasing along every one-step transition. -/
def StepPotentialNondecreasing
    (M : MarketSystem σ) (P : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → P s ≤ P t

/-- The potential account is nondecreasing along every certified finite trace. -/
def TracePotentialNondecreasing
    (M : MarketSystem σ) (P : σ → Rat) : Prop :=
  ∀ {s t : σ}, Trace M s t → P s ≤ P t

theorem stepValueBoundedByPotential_const_zero_of_stepValueNonincreasing
    (M : MarketSystem σ) (V : σ → Rat)
    (hNoninc : StepValueNonincreasing M V) :
    StepValueBoundedByPotential M V (fun _ => 0) := by
  intro s t hStep
  have hLe : V t - V s ≤ 0 := sub_nonpos.mpr (hNoninc hStep)
  simpa using hLe

theorem tracePotentialNondecreasing_of_stepPotentialNondecreasing
    (M : MarketSystem σ) (P : σ → Rat)
    (hStepPot : StepPotentialNondecreasing M P) :
    TracePotentialNondecreasing M P := by
  intro s t hTrace
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact ih.trans (hStepPot hStep)

theorem traceValue_le_potentialDrop_of_stepValueBoundedByPotential
    (M : MarketSystem σ) (V P : σ → Rat)
    (hBound : StepValueBoundedByPotential M V P)
    {s t : σ} (hTrace : Trace M s t) :
    traceValue V hTrace ≤ P s - P t := by
  induction hTrace with
  | nil =>
      simp [traceValue]
  | snoc hTrace hStep ih =>
      have hStepBound := hBound hStep
      unfold traceValue at ih hStepBound ⊢
      linarith

theorem traceValue_le_initialPotential_of_stepValueBoundedByPotential
    (M : MarketSystem σ) (V P : σ → Rat)
    (hBound : StepValueBoundedByPotential M V P)
    {s t : σ} (hTrace : Trace M s t)
    (hTerminalNonneg : 0 ≤ P t) :
    traceValue V hTrace ≤ P s := by
  have hDrop :=
    traceValue_le_potentialDrop_of_stepValueBoundedByPotential
      M V P hBound hTrace
  unfold traceValue at hDrop ⊢
  linarith

theorem noPositiveTraceValue_of_stepValueBoundedByPotential_traceNondecreasing
    (M : MarketSystem σ) (V P : σ → Rat)
    (hBound : StepValueBoundedByPotential M V P)
    (hPot : TracePotentialNondecreasing M P) :
    NoPositiveTraceValue M V := by
  intro s t hTrace
  have hDrop :=
    traceValue_le_potentialDrop_of_stepValueBoundedByPotential
      M V P hBound hTrace
  have hPotTrace : P s ≤ P t := hPot hTrace
  unfold traceValue at hDrop ⊢
  linarith

theorem noPositiveTraceValue_of_stepValueBoundedByPotential_stepNondecreasing
    (M : MarketSystem σ) (V P : σ → Rat)
    (hBound : StepValueBoundedByPotential M V P)
    (hPot : StepPotentialNondecreasing M P) :
    NoPositiveTraceValue M V :=
  noPositiveTraceValue_of_stepValueBoundedByPotential_traceNondecreasing
    M V P hBound
    (tracePotentialNondecreasing_of_stepPotentialNondecreasing M P hPot)

theorem not_hasPositiveTraceValue_of_stepValueBoundedByPotential_stepNondecreasing
    (M : MarketSystem σ) (V P : σ → Rat)
    (hBound : StepValueBoundedByPotential M V P)
    (hPot : StepPotentialNondecreasing M P) :
    ¬ HasPositiveTraceValue M V :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue M V
    (noPositiveTraceValue_of_stepValueBoundedByPotential_stepNondecreasing
      M V P hBound hPot)

end MarketSystem

end DeFi

end LeanMathlib
