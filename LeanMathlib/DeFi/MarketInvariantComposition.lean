import LeanMathlib.DeFi.MarketInvariant

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ τ α : Type*}

/-- Synchronous product: both components take one step together. -/
def syncProduct (M₁ : MarketSystem σ) (M₂ : MarketSystem τ) : MarketSystem (σ × τ) where
  Step s t := M₁.Step s.1 t.1 ∧ M₂.Step s.2 t.2

/-- Interleaving product: exactly one component takes a step while the other is unchanged. -/
def asyncProduct (M₁ : MarketSystem σ) (M₂ : MarketSystem τ) : MarketSystem (σ × τ) where
  Step s t :=
    (M₁.Step s.1 t.1 ∧ t.2 = s.2) ∨
    (t.1 = s.1 ∧ M₂.Step s.2 t.2)

theorem syncProduct_preserves_pairInvariant
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (I₁ : σ → α) (I₂ : τ → α)
    (h₁ : M₁.PreservesInvariant I₁)
    (h₂ : M₂.PreservesInvariant I₂) :
    (syncProduct M₁ M₂).PreservesInvariant fun s => (I₁ s.1, I₂ s.2) := by
  intro s t hStep
  exact Prod.ext (h₁ hStep.1) (h₂ hStep.2)

theorem asyncProduct_preserves_pairInvariant
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (I₁ : σ → α) (I₂ : τ → α)
    (h₁ : M₁.PreservesInvariant I₁)
    (h₂ : M₂.PreservesInvariant I₂) :
    (asyncProduct M₁ M₂).PreservesInvariant fun s => (I₁ s.1, I₂ s.2) := by
  intro s t hStep
  rcases hStep with hLeft | hRight
  · exact Prod.ext (h₁ hLeft.1) (congrArg I₂ hLeft.2)
  · exact Prod.ext (congrArg I₁ hRight.1) (h₂ hRight.2)

theorem syncProduct_preserves_addInvariant [Add α]
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (I₁ : σ → α) (I₂ : τ → α)
    (h₁ : M₁.PreservesInvariant I₁)
    (h₂ : M₂.PreservesInvariant I₂) :
    (syncProduct M₁ M₂).PreservesInvariant fun s => I₁ s.1 + I₂ s.2 := by
  intro s t hStep
  calc
    I₁ t.1 + I₂ t.2 = I₁ s.1 + I₂ t.2 := by rw [h₁ hStep.1]
    _ = I₁ s.1 + I₂ s.2 := by rw [h₂ hStep.2]

theorem asyncProduct_preserves_addInvariant [Add α]
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (I₁ : σ → α) (I₂ : τ → α)
    (h₁ : M₁.PreservesInvariant I₁)
    (h₂ : M₂.PreservesInvariant I₂) :
    (asyncProduct M₁ M₂).PreservesInvariant fun s => I₁ s.1 + I₂ s.2 := by
  intro s t hStep
  rcases hStep with hLeft | hRight
  · calc
      I₁ t.1 + I₂ t.2 = I₁ s.1 + I₂ t.2 := by rw [h₁ hLeft.1]
      _ = I₁ s.1 + I₂ s.2 := by rw [hLeft.2]
  · calc
      I₁ t.1 + I₂ t.2 = I₁ s.1 + I₂ t.2 := by rw [hRight.1]
      _ = I₁ s.1 + I₂ s.2 := by rw [h₂ hRight.2]

theorem no_arbitrage_of_syncProduct_addInvariant [Preorder α] [Add α]
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (I₁ : σ → α) (I₂ : τ → α)
    (dominates : σ × τ → σ × τ → Prop)
    (h₁ : M₁.PreservesInvariant I₁)
    (h₂ : M₂.PreservesInvariant I₂)
    (hStrict :
      StrictlyIncreasesOn dominates (fun s => I₁ s.1 + I₂ s.2)) :
    ¬ (syncProduct M₁ M₂).HasArbitrage dominates :=
  no_arbitrage_of_preserved_strictInvariant
    (syncProduct M₁ M₂) (fun s => I₁ s.1 + I₂ s.2)
    dominates (syncProduct_preserves_addInvariant M₁ M₂ I₁ I₂ h₁ h₂) hStrict

theorem no_arbitrage_of_asyncProduct_addInvariant [Preorder α] [Add α]
    (M₁ : MarketSystem σ) (M₂ : MarketSystem τ)
    (I₁ : σ → α) (I₂ : τ → α)
    (dominates : σ × τ → σ × τ → Prop)
    (h₁ : M₁.PreservesInvariant I₁)
    (h₂ : M₂.PreservesInvariant I₂)
    (hStrict :
      StrictlyIncreasesOn dominates (fun s => I₁ s.1 + I₂ s.2)) :
    ¬ (asyncProduct M₁ M₂).HasArbitrage dominates :=
  no_arbitrage_of_preserved_strictInvariant
    (asyncProduct M₁ M₂) (fun s => I₁ s.1 + I₂ s.2)
    dominates (asyncProduct_preserves_addInvariant M₁ M₂ I₁ I₂ h₁ h₂) hStrict

end MarketSystem

end DeFi

end LeanMathlib
