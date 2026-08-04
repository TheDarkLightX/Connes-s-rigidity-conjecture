import LeanMathlib.DeFi.MarketInvariantComposition
import LeanMathlib.DeFi.TraceValuePotential

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ τ : Type*}

theorem syncProduct_stepValueBoundedByPotential_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ P₁ : σ → Rat) (V₂ P₂ : τ → Rat)
    (h₁ : StepValueBoundedByPotential M₁ V₁ P₁)
    (h₂ : StepValueBoundedByPotential M₂ V₂ P₂) :
    StepValueBoundedByPotential
      (syncProduct M₁ M₂)
      (fun s => V₁ s.1 + V₂ s.2)
      (fun s => P₁ s.1 + P₂ s.2) := by
  intro s t hStep
  have hV₁ := h₁ hStep.1
  have hV₂ := h₂ hStep.2
  change
    (V₁ t.1 + V₂ t.2) - (V₁ s.1 + V₂ s.2) ≤
      (P₁ s.1 + P₂ s.2) - (P₁ t.1 + P₂ t.2)
  linarith

theorem asyncProduct_stepValueBoundedByPotential_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ P₁ : σ → Rat) (V₂ P₂ : τ → Rat)
    (h₁ : StepValueBoundedByPotential M₁ V₁ P₁)
    (h₂ : StepValueBoundedByPotential M₂ V₂ P₂) :
    StepValueBoundedByPotential
      (asyncProduct M₁ M₂)
      (fun s => V₁ s.1 + V₂ s.2)
      (fun s => P₁ s.1 + P₂ s.2) := by
  intro s t hStep
  rcases hStep with hLeft | hRight
  · have hV₁ := h₁ hLeft.1
    change
      (V₁ t.1 + V₂ t.2) - (V₁ s.1 + V₂ s.2) ≤
        (P₁ s.1 + P₂ s.2) - (P₁ t.1 + P₂ t.2)
    rw [hLeft.2]
    linarith
  · have hV₂ := h₂ hRight.2
    change
      (V₁ t.1 + V₂ t.2) - (V₁ s.1 + V₂ s.2) ≤
        (P₁ s.1 + P₂ s.2) - (P₁ t.1 + P₂ t.2)
    rw [hRight.1]
    linarith

theorem syncProduct_stepPotentialNondecreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (P₁ : σ → Rat) (P₂ : τ → Rat)
    (h₁ : StepPotentialNondecreasing M₁ P₁)
    (h₂ : StepPotentialNondecreasing M₂ P₂) :
    StepPotentialNondecreasing
      (syncProduct M₁ M₂)
      (fun s => P₁ s.1 + P₂ s.2) := by
  intro s t hStep
  exact add_le_add (h₁ hStep.1) (h₂ hStep.2)

theorem asyncProduct_stepPotentialNondecreasing_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (P₁ : σ → Rat) (P₂ : τ → Rat)
    (h₁ : StepPotentialNondecreasing M₁ P₁)
    (h₂ : StepPotentialNondecreasing M₂ P₂) :
    StepPotentialNondecreasing
      (asyncProduct M₁ M₂)
      (fun s => P₁ s.1 + P₂ s.2) := by
  intro s t hStep
  rcases hStep with hLeft | hRight
  · change P₁ s.1 + P₂ s.2 ≤ P₁ t.1 + P₂ t.2
    rw [hLeft.2]
    exact add_le_add (h₁ hLeft.1) le_rfl
  · change P₁ s.1 + P₂ s.2 ≤ P₁ t.1 + P₂ t.2
    rw [hRight.1]
    exact add_le_add le_rfl (h₂ hRight.2)

theorem noPositiveTraceValue_of_syncProduct_potential_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ P₁ : σ → Rat) (V₂ P₂ : τ → Rat)
    (hBound₁ : StepValueBoundedByPotential M₁ V₁ P₁)
    (hBound₂ : StepValueBoundedByPotential M₂ V₂ P₂)
    (hPot₁ : StepPotentialNondecreasing M₁ P₁)
    (hPot₂ : StepPotentialNondecreasing M₂ P₂) :
    NoPositiveTraceValue
      (syncProduct M₁ M₂)
      (fun s => V₁ s.1 + V₂ s.2) :=
  noPositiveTraceValue_of_stepValueBoundedByPotential_stepNondecreasing
    (syncProduct M₁ M₂)
    (fun s => V₁ s.1 + V₂ s.2)
    (fun s => P₁ s.1 + P₂ s.2)
    (syncProduct_stepValueBoundedByPotential_add
      M₁ M₂ V₁ P₁ V₂ P₂ hBound₁ hBound₂)
    (syncProduct_stepPotentialNondecreasing_add
      M₁ M₂ P₁ P₂ hPot₁ hPot₂)

theorem noPositiveTraceValue_of_asyncProduct_potential_add
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (V₁ P₁ : σ → Rat) (V₂ P₂ : τ → Rat)
    (hBound₁ : StepValueBoundedByPotential M₁ V₁ P₁)
    (hBound₂ : StepValueBoundedByPotential M₂ V₂ P₂)
    (hPot₁ : StepPotentialNondecreasing M₁ P₁)
    (hPot₂ : StepPotentialNondecreasing M₂ P₂) :
    NoPositiveTraceValue
      (asyncProduct M₁ M₂)
      (fun s => V₁ s.1 + V₂ s.2) :=
  noPositiveTraceValue_of_stepValueBoundedByPotential_stepNondecreasing
    (asyncProduct M₁ M₂)
    (fun s => V₁ s.1 + V₂ s.2)
    (fun s => P₁ s.1 + P₂ s.2)
    (asyncProduct_stepValueBoundedByPotential_add
      M₁ M₂ V₁ P₁ V₂ P₂ hBound₁ hBound₂)
    (asyncProduct_stepPotentialNondecreasing_add
      M₁ M₂ P₁ P₂ hPot₁ hPot₂)

end MarketSystem

end DeFi

end LeanMathlib
