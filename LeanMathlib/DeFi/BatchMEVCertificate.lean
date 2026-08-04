import LeanMathlib.DeFi.ConvexDualCertificate
import LeanMathlib.DeFi.MarketInvariantComposition

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ τ : Type*}

structure BatchMEVCertificate
    (M : MarketSystem σ) (V dual : σ → Rat) (slack budget : Rat) : Prop where
  stepBound : StepValueBoundedByDual M V dual slack
  budgetBound :
    ∀ {n : Nat} {s t : σ}, TraceN M n s t →
      dual s - dual t + (n : Rat) * slack ≤ budget

theorem traceValue_le_of_batchMEVCertificate
    {M : MarketSystem σ} {V dual : σ → Rat} {slack budget : Rat}
    (cert : BatchMEVCertificate M V dual slack budget)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceValue V hTrace.toTrace ≤ budget :=
  traceValue_le_dualBudget M V dual slack budget
    cert.stepBound hTrace (cert.budgetBound hTrace)

theorem noPositiveTraceValue_of_nonpos_batchMEVCertificate
    {M : MarketSystem σ} {V dual : σ → Rat} {slack budget : Rat}
    (cert : BatchMEVCertificate M V dual slack budget)
    (hBudget : budget ≤ 0) :
    NoPositiveTraceValue M V := by
  apply noPositiveTraceValue_of_dualDrop_nonpos M V dual slack cert.stepBound
  intro n s t hTrace
  exact (cert.budgetBound hTrace).trans hBudget

theorem not_hasPositiveTraceValue_of_nonpos_batchMEVCertificate
    {M : MarketSystem σ} {V dual : σ → Rat} {slack budget : Rat}
    (cert : BatchMEVCertificate M V dual slack budget)
    (hBudget : budget ≤ 0) :
    ¬ HasPositiveTraceValue M V :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue M V
    (noPositiveTraceValue_of_nonpos_batchMEVCertificate cert hBudget)

theorem stepValueBoundedByDual_add
    {M : MarketSystem σ} {V₁ V₂ dual₁ dual₂ : σ → Rat}
    {slack₁ slack₂ : Rat}
    (h₁ : StepValueBoundedByDual M V₁ dual₁ slack₁)
    (h₂ : StepValueBoundedByDual M V₂ dual₂ slack₂) :
    StepValueBoundedByDual M
      (fun s => V₁ s + V₂ s)
      (fun s => dual₁ s + dual₂ s)
      (slack₁ + slack₂) := by
  intro s t hStep
  have hBound₁ := h₁ hStep
  have hBound₂ := h₂ hStep
  change
    (V₁ t + V₂ t) - (V₁ s + V₂ s) ≤
      (dual₁ s + dual₂ s) - (dual₁ t + dual₂ t) + (slack₁ + slack₂)
  linarith

theorem batchMEVCertificate_add
    {M : MarketSystem σ}
    {V₁ V₂ dual₁ dual₂ : σ → Rat}
    {slack₁ slack₂ budget₁ budget₂ : Rat}
    (cert₁ : BatchMEVCertificate M V₁ dual₁ slack₁ budget₁)
    (cert₂ : BatchMEVCertificate M V₂ dual₂ slack₂ budget₂) :
    BatchMEVCertificate M
      (fun s => V₁ s + V₂ s)
      (fun s => dual₁ s + dual₂ s)
      (slack₁ + slack₂)
      (budget₁ + budget₂) where
  stepBound := stepValueBoundedByDual_add cert₁.stepBound cert₂.stepBound
  budgetBound := by
    intro n s t hTrace
    have hBudget₁ := cert₁.budgetBound hTrace
    have hBudget₂ := cert₂.budgetBound hTrace
    linarith

theorem noPositiveTraceValue_of_add_batchMEVCertificates
    {M : MarketSystem σ}
    {V₁ V₂ dual₁ dual₂ : σ → Rat}
    {slack₁ slack₂ budget₁ budget₂ : Rat}
    (cert₁ : BatchMEVCertificate M V₁ dual₁ slack₁ budget₁)
    (cert₂ : BatchMEVCertificate M V₂ dual₂ slack₂ budget₂)
    (hBudget : budget₁ + budget₂ ≤ 0) :
    NoPositiveTraceValue M (fun s => V₁ s + V₂ s) :=
  noPositiveTraceValue_of_nonpos_batchMEVCertificate
    (batchMEVCertificate_add cert₁ cert₂) hBudget

theorem stepValueBoundedByDual_of_stepIncluded
    {M N : MarketSystem σ} {V dual : σ → Rat} {slack : Rat}
    (hInc : StepIncluded M N)
    (hStep : StepValueBoundedByDual N V dual slack) :
    StepValueBoundedByDual M V dual slack := by
  intro s t hLocal
  exact hStep (hInc hLocal)

theorem batchMEVCertificate_of_stepIncluded
    {M N : MarketSystem σ} {V dual : σ → Rat} {slack budget : Rat}
    (hInc : StepIncluded M N)
    (cert : BatchMEVCertificate N V dual slack budget) :
    BatchMEVCertificate M V dual slack budget where
  stepBound := stepValueBoundedByDual_of_stepIncluded hInc cert.stepBound
  budgetBound := by
    intro n s t hTrace
    exact cert.budgetBound (TraceN.mono hInc hTrace)

theorem noPositiveTraceValue_of_stepIncluded_batchMEVCertificate
    {M N : MarketSystem σ} {V dual : σ → Rat} {slack budget : Rat}
    (hInc : StepIncluded M N)
    (cert : BatchMEVCertificate N V dual slack budget)
    (hBudget : budget ≤ 0) :
    NoPositiveTraceValue M V :=
  noPositiveTraceValue_of_nonpos_batchMEVCertificate
    (batchMEVCertificate_of_stepIncluded hInc cert) hBudget

namespace TraceN

theorem syncProduct_left
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {n : Nat} {s t : σ × τ}
    (hTrace : TraceN (syncProduct M₁ M₂) n s t) :
    TraceN M₁ n s.1 t.1 := by
  induction hTrace with
  | nil s =>
      exact TraceN.nil s.1
  | snoc hTrace hStep ih =>
      exact TraceN.snoc ih hStep.1

theorem syncProduct_right
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {n : Nat} {s t : σ × τ}
    (hTrace : TraceN (syncProduct M₁ M₂) n s t) :
    TraceN M₂ n s.2 t.2 := by
  induction hTrace with
  | nil s =>
      exact TraceN.nil s.2
  | snoc hTrace hStep ih =>
      exact TraceN.snoc ih hStep.2

end TraceN

theorem stepValueBoundedByDual_syncProduct_add
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {V₁ dual₁ : σ → Rat} {V₂ dual₂ : τ → Rat}
    {slack₁ slack₂ : Rat}
    (h₁ : StepValueBoundedByDual M₁ V₁ dual₁ slack₁)
    (h₂ : StepValueBoundedByDual M₂ V₂ dual₂ slack₂) :
    StepValueBoundedByDual
      (syncProduct M₁ M₂)
      (fun s : σ × τ => V₁ s.1 + V₂ s.2)
      (fun s : σ × τ => dual₁ s.1 + dual₂ s.2)
      (slack₁ + slack₂) := by
  intro s t hStep
  have hBound₁ := h₁ hStep.1
  have hBound₂ := h₂ hStep.2
  change
    (V₁ t.1 + V₂ t.2) - (V₁ s.1 + V₂ s.2) ≤
      (dual₁ s.1 + dual₂ s.2) -
        (dual₁ t.1 + dual₂ t.2) + (slack₁ + slack₂)
  linarith

theorem batchMEVCertificate_syncProduct_add
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {V₁ dual₁ : σ → Rat} {V₂ dual₂ : τ → Rat}
    {slack₁ slack₂ budget₁ budget₂ : Rat}
    (cert₁ : BatchMEVCertificate M₁ V₁ dual₁ slack₁ budget₁)
    (cert₂ : BatchMEVCertificate M₂ V₂ dual₂ slack₂ budget₂) :
    BatchMEVCertificate
      (syncProduct M₁ M₂)
      (fun s : σ × τ => V₁ s.1 + V₂ s.2)
      (fun s : σ × τ => dual₁ s.1 + dual₂ s.2)
      (slack₁ + slack₂)
      (budget₁ + budget₂) where
  stepBound :=
    stepValueBoundedByDual_syncProduct_add cert₁.stepBound cert₂.stepBound
  budgetBound := by
    intro n s t hTrace
    have hBudget₁ := cert₁.budgetBound (TraceN.syncProduct_left hTrace)
    have hBudget₂ := cert₂.budgetBound (TraceN.syncProduct_right hTrace)
    change
      (dual₁ s.1 + dual₂ s.2) - (dual₁ t.1 + dual₂ t.2) +
          (n : Rat) * (slack₁ + slack₂) ≤
        budget₁ + budget₂
    ring_nf at hBudget₁ hBudget₂ ⊢
    linarith

theorem noPositiveTraceValue_of_syncProduct_batchMEVCertificates
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {V₁ dual₁ : σ → Rat} {V₂ dual₂ : τ → Rat}
    {slack₁ slack₂ budget₁ budget₂ : Rat}
    (cert₁ : BatchMEVCertificate M₁ V₁ dual₁ slack₁ budget₁)
    (cert₂ : BatchMEVCertificate M₂ V₂ dual₂ slack₂ budget₂)
    (hBudget : budget₁ + budget₂ ≤ 0) :
    NoPositiveTraceValue
      (syncProduct M₁ M₂)
      (fun s : σ × τ => V₁ s.1 + V₂ s.2) :=
  noPositiveTraceValue_of_nonpos_batchMEVCertificate
    (batchMEVCertificate_syncProduct_add cert₁ cert₂) hBudget

end MarketSystem

end DeFi

end LeanMathlib
