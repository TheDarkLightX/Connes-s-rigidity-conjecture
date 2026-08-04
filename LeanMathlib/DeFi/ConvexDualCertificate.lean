import LeanMathlib.DeFi.TokenomicsSupply

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

def StepValueBoundedByDual
    (M : MarketSystem σ) (V dual : σ → Rat) (slack : Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → V t - V s ≤ dual s - dual t + slack

theorem traceValue_le_dualDrop_add_slack
    (M : MarketSystem σ) (V dual : σ → Rat) (slack : Rat)
    (hStep : StepValueBoundedByDual M V dual slack)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceValue V hTrace.toTrace ≤ dual s - dual t + (n : Rat) * slack := by
  induction hTrace with
  | nil =>
      simp [traceValue]
  | snoc hTrace hStepOne ih =>
      have hLocal := hStep hStepOne
      unfold traceValue at ih hLocal ⊢
      norm_num
      linarith

theorem traceValue_le_dualBudget
    (M : MarketSystem σ) (V dual : σ → Rat) (slack budget : Rat)
    (hStep : StepValueBoundedByDual M V dual slack)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hBudget : dual s - dual t + (n : Rat) * slack ≤ budget) :
    traceValue V hTrace.toTrace ≤ budget :=
  (traceValue_le_dualDrop_add_slack M V dual slack hStep hTrace).trans hBudget

theorem exists_traceN_of_trace
    {M : MarketSystem σ} {s t : σ} (hTrace : Trace M s t) :
    ∃ n : Nat, TraceN M n s t := by
  induction hTrace with
  | nil =>
      exact ⟨0, TraceN.nil _⟩
  | snoc hTrace hStep ih =>
      rcases ih with ⟨n, hTraceN⟩
      exact ⟨n + 1, TraceN.snoc hTraceN hStep⟩

theorem noPositiveTraceValue_of_dualDrop_nonpos
    (M : MarketSystem σ) (V dual : σ → Rat) (slack : Rat)
    (hStep : StepValueBoundedByDual M V dual slack)
    (hBound :
      ∀ {n : Nat} {s t : σ}, TraceN M n s t →
        dual s - dual t + (n : Rat) * slack ≤ 0) :
    NoPositiveTraceValue M V := by
  intro s t hTrace
  rcases exists_traceN_of_trace hTrace with ⟨n, hTraceN⟩
  have hLe := traceValue_le_dualDrop_add_slack M V dual slack hStep hTraceN
  have hBudget := hBound hTraceN
  simpa using hLe.trans hBudget

theorem traceValue_nonpos_of_traceN_dualDrop_nonpos
    (M : MarketSystem σ) (V dual : σ → Rat) (slack : Rat)
    (hStep : StepValueBoundedByDual M V dual slack)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hBound : dual s - dual t + (n : Rat) * slack ≤ 0) :
    traceValue V hTrace.toTrace ≤ 0 :=
  traceValue_le_dualBudget M V dual slack 0 hStep hTrace hBound

theorem traceValue_nonpos_of_dualNonincreasing_zeroSlack
    (M : MarketSystem σ) (V dual : σ → Rat)
    (hStep : StepValueBoundedByDual M V dual 0)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hDual : dual s ≤ dual t) :
    traceValue V hTrace.toTrace ≤ 0 := by
  apply traceValue_nonpos_of_traceN_dualDrop_nonpos M V dual 0 hStep hTrace
  have hDrop : dual s - dual t ≤ 0 := sub_nonpos.mpr hDual
  simpa using hDrop

theorem not_hasPositiveTraceValue_of_dualCertificate
    (M : MarketSystem σ) (V dual : σ → Rat)
    (hStep : StepValueBoundedByDual M V dual 0)
    (hDual : ∀ {s t : σ}, Trace M s t → dual s ≤ dual t) :
    ¬ HasPositiveTraceValue M V := by
  rintro ⟨s, t, hTrace, hPos⟩
  have hLe : traceValue V hTrace ≤ 0 := by
    rcases exists_traceN_of_trace hTrace with ⟨n, hTraceN⟩
    have hBounded :=
      traceValue_le_dualDrop_add_slack M V dual 0 hStep hTraceN
    have hDualTrace : dual s ≤ dual t := hDual hTrace
    have hDrop : dual s - dual t + (n : Rat) * 0 ≤ 0 := by
      have hDropOnly : dual s - dual t ≤ 0 := sub_nonpos.mpr hDualTrace
      simpa using hDropOnly
    exact hBounded.trans hDrop
  exact (not_lt_of_ge hLe) hPos

end MarketSystem

end DeFi

end LeanMathlib
