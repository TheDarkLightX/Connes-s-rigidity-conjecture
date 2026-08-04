import LeanMathlib.DeFi.TraceValue

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- A true value function is pointwise bounded by conservative lower and upper functions. -/
def ValueSandwiched (lower V upper : σ → Rat) : Prop :=
  ∀ s : σ, lower s ≤ V s ∧ V s ≤ upper s

/-- Every certified trace has terminal upper value at most initial lower value. -/
def TraceUpperBoundedByInitialLower
    (M : MarketSystem σ) (lower upper : σ → Rat) : Prop :=
  ∀ {s t : σ}, Trace M s t → upper t ≤ lower s

theorem traceValue_le_upperMinusLower_of_sandwiched
    {M : MarketSystem σ} {lower V upper : σ → Rat}
    (hSand : ValueSandwiched lower V upper)
    {s t : σ} (hTrace : Trace M s t) :
    traceValue V hTrace ≤ upper t - lower s := by
  have hs : lower s ≤ V s := (hSand s).1
  have ht : V t ≤ upper t := (hSand t).2
  unfold traceValue
  linarith

theorem traceValue_le_bound_of_sandwiched
    {M : MarketSystem σ} {lower V upper : σ → Rat}
    (hSand : ValueSandwiched lower V upper)
    {s t : σ} (hTrace : Trace M s t)
    {bound : Rat} (hBound : upper t - lower s ≤ bound) :
    traceValue V hTrace ≤ bound :=
  (traceValue_le_upperMinusLower_of_sandwiched hSand hTrace).trans hBound

theorem traceValue_nonpos_of_sandwiched_upper_le_lower
    {M : MarketSystem σ} {lower V upper : σ → Rat}
    (hSand : ValueSandwiched lower V upper)
    {s t : σ} (hTrace : Trace M s t)
    (hUpperLower : upper t ≤ lower s) :
    traceValue V hTrace ≤ 0 := by
  have hBound : upper t - lower s ≤ 0 := sub_nonpos.mpr hUpperLower
  exact traceValue_le_bound_of_sandwiched hSand hTrace hBound

theorem noPositiveTraceValue_of_sandwiched_traceUpperBounded
    (M : MarketSystem σ) (lower V upper : σ → Rat)
    (hSand : ValueSandwiched lower V upper)
    (hTraceBound : TraceUpperBoundedByInitialLower M lower upper) :
    NoPositiveTraceValue M V := by
  intro s t hTrace
  exact traceValue_nonpos_of_sandwiched_upper_le_lower
    hSand hTrace (hTraceBound hTrace)

theorem not_hasPositiveTraceValue_of_sandwiched_traceUpperBounded
    (M : MarketSystem σ) (lower V upper : σ → Rat)
    (hSand : ValueSandwiched lower V upper)
    (hTraceBound : TraceUpperBoundedByInitialLower M lower upper) :
    ¬ HasPositiveTraceValue M V :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue M V
    (noPositiveTraceValue_of_sandwiched_traceUpperBounded
      M lower V upper hSand hTraceBound)

theorem positive_upperMinusLower_of_positive_traceValue_sandwiched
    {M : MarketSystem σ} {lower V upper : σ → Rat}
    (hSand : ValueSandwiched lower V upper)
    {s t : σ} (hTrace : Trace M s t)
    (hPos : 0 < traceValue V hTrace) :
    0 < upper t - lower s := by
  have hLe := traceValue_le_upperMinusLower_of_sandwiched hSand hTrace
  exact hPos.trans_le hLe

theorem hasPositiveTraceValue_witnesses_positive_sandwich_gap
    (M : MarketSystem σ) (lower V upper : σ → Rat)
    (hSand : ValueSandwiched lower V upper)
    (hPos : HasPositiveTraceValue M V) :
    ∃ s t : σ, ∃ _hTrace : Trace M s t, 0 < upper t - lower s := by
  rcases hPos with ⟨s, t, hTrace, hValue⟩
  exact ⟨s, t, hTrace,
    positive_upperMinusLower_of_positive_traceValue_sandwiched hSand hTrace hValue⟩

theorem not_hasPositiveTraceValue_of_no_positive_sandwich_gap
    (M : MarketSystem σ) (lower V upper : σ → Rat)
    (hSand : ValueSandwiched lower V upper)
    (hNoGap : ∀ {s t : σ}, Trace M s t → upper t ≤ lower s) :
    ¬ HasPositiveTraceValue M V :=
  not_hasPositiveTraceValue_of_sandwiched_traceUpperBounded
    M lower V upper hSand hNoGap

end MarketSystem

end DeFi

end LeanMathlib
