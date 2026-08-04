import LeanMathlib.DeFi.TraceValue

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- Every one-step transition is nonincreasing for the chosen value function. -/
def StepValueNonincreasing (M : MarketSystem σ) (V : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → V t ≤ V s

theorem stepValueNonincreasing_of_preservesInvariant
    (M : MarketSystem σ) (V : σ → Rat)
    (hPres : M.PreservesInvariant V) :
    StepValueNonincreasing M V := by
  intro s t hStep
  rw [hPres hStep]

theorem stepValueNonincreasing_of_stepIncluded
    {M N : MarketSystem σ} (V : σ → Rat)
    (hInc : StepIncluded M N)
    (hNoninc : StepValueNonincreasing N V) :
    StepValueNonincreasing M V := by
  intro s t hStep
  exact hNoninc (hInc hStep)

theorem value_le_of_trace_stepValueNonincreasing
    (M : MarketSystem σ) (V : σ → Rat)
    (hNoninc : StepValueNonincreasing M V)
    {s t : σ} (hTrace : Trace M s t) :
    V t ≤ V s := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact (hNoninc hStep).trans ih

theorem traceValue_nonpos_of_stepValueNonincreasing
    (M : MarketSystem σ) (V : σ → Rat)
    (hNoninc : StepValueNonincreasing M V)
    {s t : σ} (hTrace : Trace M s t) :
    traceValue V hTrace ≤ 0 := by
  have hLe : V t ≤ V s :=
    value_le_of_trace_stepValueNonincreasing M V hNoninc hTrace
  unfold traceValue
  exact sub_nonpos.mpr hLe

theorem noPositiveTraceValue_of_stepValueNonincreasing
    (M : MarketSystem σ) (V : σ → Rat)
    (hNoninc : StepValueNonincreasing M V) :
    NoPositiveTraceValue M V := by
  intro s t hTrace
  exact traceValue_nonpos_of_stepValueNonincreasing M V hNoninc hTrace

theorem not_hasPositiveTraceValue_of_stepValueNonincreasing
    (M : MarketSystem σ) (V : σ → Rat)
    (hNoninc : StepValueNonincreasing M V) :
    ¬ HasPositiveTraceValue M V :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue M V
    (noPositiveTraceValue_of_stepValueNonincreasing M V hNoninc)

end MarketSystem

end DeFi

end LeanMathlib
