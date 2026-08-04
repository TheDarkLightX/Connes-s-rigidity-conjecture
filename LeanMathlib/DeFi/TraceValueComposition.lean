import LeanMathlib.DeFi.MarketInvariantComposition
import LeanMathlib.DeFi.TraceValueBounds

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ τ : Type*}

theorem syncProduct_stepValueNonincreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ : σ → Rat) (V₂ : τ → Rat)
    (h₁ : StepValueNonincreasing M₁ V₁)
    (h₂ : StepValueNonincreasing M₂ V₂) :
    StepValueNonincreasing (syncProduct M₁ M₂) fun s => V₁ s.1 + V₂ s.2 := by
  intro s t hStep
  exact add_le_add (h₁ hStep.1) (h₂ hStep.2)

theorem asyncProduct_stepValueNonincreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ : σ → Rat) (V₂ : τ → Rat)
    (h₁ : StepValueNonincreasing M₁ V₁)
    (h₂ : StepValueNonincreasing M₂ V₂) :
    StepValueNonincreasing (asyncProduct M₁ M₂) fun s => V₁ s.1 + V₂ s.2 := by
  intro s t hStep
  rcases hStep with hLeft | hRight
  · change V₁ t.1 + V₂ t.2 ≤ V₁ s.1 + V₂ s.2
    rw [hLeft.2]
    exact add_le_add (h₁ hLeft.1) le_rfl
  · change V₁ t.1 + V₂ t.2 ≤ V₁ s.1 + V₂ s.2
    rw [hRight.1]
    exact add_le_add le_rfl (h₂ hRight.2)

theorem noPositiveTraceValue_of_syncProduct_stepValueNonincreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ : σ → Rat) (V₂ : τ → Rat)
    (h₁ : StepValueNonincreasing M₁ V₁)
    (h₂ : StepValueNonincreasing M₂ V₂) :
    NoPositiveTraceValue (syncProduct M₁ M₂) fun s => V₁ s.1 + V₂ s.2 :=
  noPositiveTraceValue_of_stepValueNonincreasing
    (syncProduct M₁ M₂) (fun s => V₁ s.1 + V₂ s.2)
    (syncProduct_stepValueNonincreasing_add M₁ M₂ V₁ V₂ h₁ h₂)

theorem noPositiveTraceValue_of_asyncProduct_stepValueNonincreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ : σ → Rat) (V₂ : τ → Rat)
    (h₁ : StepValueNonincreasing M₁ V₁)
    (h₂ : StepValueNonincreasing M₂ V₂) :
    NoPositiveTraceValue (asyncProduct M₁ M₂) fun s => V₁ s.1 + V₂ s.2 :=
  noPositiveTraceValue_of_stepValueNonincreasing
    (asyncProduct M₁ M₂) (fun s => V₁ s.1 + V₂ s.2)
    (asyncProduct_stepValueNonincreasing_add M₁ M₂ V₁ V₂ h₁ h₂)

theorem not_hasPositiveTraceValue_of_syncProduct_stepValueNonincreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ : σ → Rat) (V₂ : τ → Rat)
    (h₁ : StepValueNonincreasing M₁ V₁)
    (h₂ : StepValueNonincreasing M₂ V₂) :
    ¬ HasPositiveTraceValue (syncProduct M₁ M₂) (fun s => V₁ s.1 + V₂ s.2) :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue
    (syncProduct M₁ M₂) (fun s => V₁ s.1 + V₂ s.2)
    (noPositiveTraceValue_of_syncProduct_stepValueNonincreasing_add M₁ M₂ V₁ V₂ h₁ h₂)

theorem not_hasPositiveTraceValue_of_asyncProduct_stepValueNonincreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ : σ → Rat) (V₂ : τ → Rat)
    (h₁ : StepValueNonincreasing M₁ V₁)
    (h₂ : StepValueNonincreasing M₂ V₂) :
    ¬ HasPositiveTraceValue (asyncProduct M₁ M₂) (fun s => V₁ s.1 + V₂ s.2) :=
  not_hasPositiveTraceValue_of_noPositiveTraceValue
    (asyncProduct M₁ M₂) (fun s => V₁ s.1 + V₂ s.2)
    (noPositiveTraceValue_of_asyncProduct_stepValueNonincreasing_add M₁ M₂ V₁ V₂ h₁ h₂)

end MarketSystem

end DeFi

end LeanMathlib
