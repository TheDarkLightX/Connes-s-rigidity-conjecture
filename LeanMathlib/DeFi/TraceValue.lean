import LeanMathlib.DeFi.MarketInvariant

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- One market transition relation is included in another. -/
def StepIncluded (M N : MarketSystem σ) : Prop :=
  ∀ {s t : σ}, M.Step s t → N.Step s t

theorem stepIncluded_refl (M : MarketSystem σ) :
    StepIncluded M M := by
  intro s t hStep
  exact hStep

theorem stepIncluded_trans (L M N : MarketSystem σ)
    (hLM : StepIncluded L M) (hMN : StepIncluded M N) :
    StepIncluded L N := by
  intro s t hStep
  exact hMN (hLM hStep)

/-- A proof object for a finite market execution. -/
inductive Trace (M : MarketSystem σ) : σ → σ → Prop
  | nil (s : σ) : Trace M s s
  | snoc {s t u : σ} : Trace M s t → M.Step t u → Trace M s u

namespace Trace

theorem single {M : MarketSystem σ} {s t : σ}
    (hStep : M.Step s t) :
    Trace M s t :=
  Trace.snoc (Trace.nil s) hStep

theorem toReachable {M : MarketSystem σ} {s t : σ}
    (hTrace : Trace M s t) :
    M.Reachable s t := by
  induction hTrace with
  | nil =>
      exact Reachable.refl _
  | snoc hTrace hStep ih =>
      exact Reachable.tail ih hStep

theorem ofReachable {M : MarketSystem σ} {s t : σ}
    (hReach : M.Reachable s t) :
    Trace M s t := by
  induction hReach with
  | refl =>
      exact Trace.nil _
  | tail hReach hStep ih =>
      exact Trace.snoc ih hStep

theorem reachable_iff_trace (M : MarketSystem σ) {s t : σ} :
    M.Reachable s t ↔ Trace M s t :=
  ⟨Trace.ofReachable, Trace.toReachable⟩

theorem mono {M N : MarketSystem σ}
    (hInc : StepIncluded M N) {s t : σ}
    (hTrace : Trace M s t) :
    Trace N s t := by
  induction hTrace with
  | nil =>
      exact Trace.nil _
  | snoc hTrace hStep ih =>
      exact Trace.snoc ih (hInc hStep)

end Trace

/-- Terminal value change along a certified finite trace. -/
def traceValue {M : MarketSystem σ} (V : σ → Rat)
    {s t : σ} (_hTrace : Trace M s t) : Rat :=
  V t - V s

/-- No finite trace has positive terminal value change. -/
def NoPositiveTraceValue (M : MarketSystem σ) (V : σ → Rat) : Prop :=
  ∀ {s t : σ} (hTrace : Trace M s t), traceValue V hTrace ≤ 0

/-- Some finite trace has positive terminal value change. -/
def HasPositiveTraceValue (M : MarketSystem σ) (V : σ → Rat) : Prop :=
  ∃ s t : σ, ∃ hTrace : Trace M s t, 0 < traceValue V hTrace

theorem traceValue_eq_zero_of_preservedInvariant
    (M : MarketSystem σ) (V : σ → Rat)
    (hPres : M.PreservesInvariant V)
    {s t : σ} (hTrace : Trace M s t) :
    traceValue V hTrace = 0 := by
  have hEq : V t = V s :=
    invariant_eq_of_reachable M V hPres (Trace.toReachable hTrace)
  unfold traceValue
  rw [hEq]
  simp

theorem noPositiveTraceValue_of_preservedInvariant
    (M : MarketSystem σ) (V : σ → Rat)
    (hPres : M.PreservesInvariant V) :
    NoPositiveTraceValue M V := by
  intro s t hTrace
  rw [traceValue_eq_zero_of_preservedInvariant M V hPres hTrace]

theorem not_hasPositiveTraceValue_of_noPositiveTraceValue
    (M : MarketSystem σ) (V : σ → Rat)
    (hNo : NoPositiveTraceValue M V) :
    ¬ HasPositiveTraceValue M V := by
  rintro ⟨s, t, hTrace, hPos⟩
  exact (not_lt_of_ge (hNo hTrace)) hPos

theorem not_hasPositiveTraceValue_of_preservedInvariant
    (M : MarketSystem σ) (V : σ → Rat)
    (hPres : M.PreservesInvariant V) :
    ¬ HasPositiveTraceValue M V :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue M V
    (noPositiveTraceValue_of_preservedInvariant M V hPres)

theorem hasPositiveTraceValue_mono {M N : MarketSystem σ}
    (V : σ → Rat) (hInc : StepIncluded M N)
    (hPos : HasPositiveTraceValue M V) :
    HasPositiveTraceValue N V := by
  rcases hPos with ⟨s, t, hTrace, hValue⟩
  exact ⟨s, t, Trace.mono hInc hTrace, by simpa [traceValue] using hValue⟩

theorem noPositiveTraceValue_of_stepIncluded {M N : MarketSystem σ}
    (V : σ → Rat) (hInc : StepIncluded M N)
    (hNo : NoPositiveTraceValue N V) :
    NoPositiveTraceValue M V := by
  intro s t hTrace
  simpa [traceValue] using hNo (Trace.mono hInc hTrace)

theorem hasPositiveTraceValue_of_reachable_value
    {M : MarketSystem σ} (V : σ → Rat)
    {s t : σ} (hReach : M.Reachable s t)
    (hValue : 0 < V t - V s) :
    HasPositiveTraceValue M V :=
  ⟨s, t, Trace.ofReachable hReach, by simpa [traceValue] using hValue⟩

end MarketSystem

end DeFi

end LeanMathlib
