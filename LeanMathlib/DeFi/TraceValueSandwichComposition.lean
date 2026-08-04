import LeanMathlib.DeFi.MarketInvariantComposition
import LeanMathlib.DeFi.TraceValueSandwich

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

namespace Trace

variable {σ τ : Type*}

theorem syncProduct_left
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {s t : σ × τ}
    (hTrace : Trace (syncProduct M₁ M₂) s t) :
    Trace M₁ s.1 t.1 := by
  induction hTrace with
  | nil =>
      exact Trace.nil _
  | snoc hTrace hStep ih =>
      exact Trace.snoc ih hStep.1

theorem syncProduct_right
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {s t : σ × τ}
    (hTrace : Trace (syncProduct M₁ M₂) s t) :
    Trace M₂ s.2 t.2 := by
  induction hTrace with
  | nil =>
      exact Trace.nil _
  | snoc hTrace hStep ih =>
      exact Trace.snoc ih hStep.2

theorem asyncProduct_left
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {s t : σ × τ}
    (hTrace : Trace (asyncProduct M₁ M₂) s t) :
    Trace M₁ s.1 t.1 := by
  induction hTrace with
  | nil =>
      exact Trace.nil _
  | snoc hTrace hStep ih =>
      rcases hStep with hLeft | hRight
      · exact Trace.snoc ih hLeft.1
      · rw [hRight.1]
        exact ih

theorem asyncProduct_right
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {s t : σ × τ}
    (hTrace : Trace (asyncProduct M₁ M₂) s t) :
    Trace M₂ s.2 t.2 := by
  induction hTrace with
  | nil =>
      exact Trace.nil _
  | snoc hTrace hStep ih =>
      rcases hStep with hLeft | hRight
      · rw [hLeft.2]
        exact ih
      · exact Trace.snoc ih hRight.2

end Trace

variable {σ τ : Type*}

theorem productValueSandwiched_add
    {lower₁ V₁ upper₁ : σ → Rat}
    {lower₂ V₂ upper₂ : τ → Rat}
    (h₁ : ValueSandwiched lower₁ V₁ upper₁)
    (h₂ : ValueSandwiched lower₂ V₂ upper₂) :
    ValueSandwiched
      (fun s : σ × τ => lower₁ s.1 + lower₂ s.2)
      (fun s => V₁ s.1 + V₂ s.2)
      (fun s => upper₁ s.1 + upper₂ s.2) := by
  intro s
  exact ⟨add_le_add (h₁ s.1).1 (h₂ s.2).1,
    add_le_add (h₁ s.1).2 (h₂ s.2).2⟩

theorem syncProduct_traceUpperBoundedByInitialLower_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (lower₁ upper₁ : σ → Rat) (lower₂ upper₂ : τ → Rat)
    (h₁ : TraceUpperBoundedByInitialLower M₁ lower₁ upper₁)
    (h₂ : TraceUpperBoundedByInitialLower M₂ lower₂ upper₂) :
    TraceUpperBoundedByInitialLower
      (syncProduct M₁ M₂)
      (fun s => lower₁ s.1 + lower₂ s.2)
      (fun s => upper₁ s.1 + upper₂ s.2) := by
  intro s t hTrace
  exact add_le_add
    (h₁ (Trace.syncProduct_left hTrace))
    (h₂ (Trace.syncProduct_right hTrace))

theorem asyncProduct_traceUpperBoundedByInitialLower_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (lower₁ upper₁ : σ → Rat) (lower₂ upper₂ : τ → Rat)
    (h₁ : TraceUpperBoundedByInitialLower M₁ lower₁ upper₁)
    (h₂ : TraceUpperBoundedByInitialLower M₂ lower₂ upper₂) :
    TraceUpperBoundedByInitialLower
      (asyncProduct M₁ M₂)
      (fun s => lower₁ s.1 + lower₂ s.2)
      (fun s => upper₁ s.1 + upper₂ s.2) := by
  intro s t hTrace
  exact add_le_add
    (h₁ (Trace.asyncProduct_left hTrace))
    (h₂ (Trace.asyncProduct_right hTrace))

theorem noPositiveTraceValue_of_syncProduct_sandwiched_traceUpperBounded_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (lower₁ V₁ upper₁ : σ → Rat) (lower₂ V₂ upper₂ : τ → Rat)
    (hSand₁ : ValueSandwiched lower₁ V₁ upper₁)
    (hSand₂ : ValueSandwiched lower₂ V₂ upper₂)
    (hBound₁ : TraceUpperBoundedByInitialLower M₁ lower₁ upper₁)
    (hBound₂ : TraceUpperBoundedByInitialLower M₂ lower₂ upper₂) :
    NoPositiveTraceValue (syncProduct M₁ M₂) fun s => V₁ s.1 + V₂ s.2 :=
  noPositiveTraceValue_of_sandwiched_traceUpperBounded
    (syncProduct M₁ M₂)
    (fun s => lower₁ s.1 + lower₂ s.2)
    (fun s => V₁ s.1 + V₂ s.2)
    (fun s => upper₁ s.1 + upper₂ s.2)
    (productValueSandwiched_add hSand₁ hSand₂)
    (syncProduct_traceUpperBoundedByInitialLower_add
      M₁ M₂ lower₁ upper₁ lower₂ upper₂ hBound₁ hBound₂)

theorem noPositiveTraceValue_of_asyncProduct_sandwiched_traceUpperBounded_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (lower₁ V₁ upper₁ : σ → Rat) (lower₂ V₂ upper₂ : τ → Rat)
    (hSand₁ : ValueSandwiched lower₁ V₁ upper₁)
    (hSand₂ : ValueSandwiched lower₂ V₂ upper₂)
    (hBound₁ : TraceUpperBoundedByInitialLower M₁ lower₁ upper₁)
    (hBound₂ : TraceUpperBoundedByInitialLower M₂ lower₂ upper₂) :
    NoPositiveTraceValue (asyncProduct M₁ M₂) fun s => V₁ s.1 + V₂ s.2 :=
  noPositiveTraceValue_of_sandwiched_traceUpperBounded
    (asyncProduct M₁ M₂)
    (fun s => lower₁ s.1 + lower₂ s.2)
    (fun s => V₁ s.1 + V₂ s.2)
    (fun s => upper₁ s.1 + upper₂ s.2)
    (productValueSandwiched_add hSand₁ hSand₂)
    (asyncProduct_traceUpperBoundedByInitialLower_add
      M₁ M₂ lower₁ upper₁ lower₂ upper₂ hBound₁ hBound₂)

end MarketSystem

end DeFi

end LeanMathlib
