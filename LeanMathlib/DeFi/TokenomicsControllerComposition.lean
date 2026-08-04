import LeanMathlib.DeFi.MarketInvariantComposition
import LeanMathlib.DeFi.TokenomicsControllerGuard

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

namespace TokenomicsControllerGuard

variable {σ τ : Type*}

theorem syncProduct_add
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {A₁ S₁ T₁ : σ → Rat} {A₂ S₂ T₂ : τ → Rat} {q : Rat}
    (h₁ : TokenomicsControllerGuard M₁ A₁ S₁ T₁ q)
    (h₂ : TokenomicsControllerGuard M₂ A₂ S₂ T₂ q) :
    TokenomicsControllerGuard
      (syncProduct M₁ M₂)
      (fun s : σ × τ => A₁ s.1 + A₂ s.2)
      (fun s : σ × τ => S₁ s.1 + S₂ s.2)
      (fun s : σ × τ => T₁ s.1 + T₂ s.2)
      q where
  supplyFactor := by
    intro s t hStep
    have hSupply₁ := h₁.supplyFactor hStep.1
    have hSupply₂ := h₂.supplyFactor hStep.2
    change S₁ t.1 + S₂ t.2 ≤ q * (S₁ s.1 + S₂ s.2)
    linarith
  burnFunded := by
    intro s t hStep
    have hFund₁ := h₁.burnFunded hStep.1
    have hFund₂ := h₂.burnFunded hStep.2
    change
      (S₁ s.1 + S₂ s.2) - (S₁ t.1 + S₂ t.2) ≤
        (T₁ s.1 + T₂ s.2) - (T₁ t.1 + T₂ t.2)
    linarith
  outputNondecreasing := by
    intro s t hStep
    exact add_le_add
      (h₁.outputNondecreasing hStep.1)
      (h₂.outputNondecreasing hStep.2)
  treasuryNonnegative := by
    intro s
    exact add_nonneg (h₁.treasuryNonnegative s.1) (h₂.treasuryNonnegative s.2)
  outputNonnegative := by
    intro s
    exact add_nonneg (h₁.outputNonnegative s.1) (h₂.outputNonnegative s.2)
  supplyPositive := by
    intro s
    exact add_pos (h₁.supplyPositive s.1) (h₂.supplyPositive s.2)

theorem asyncProduct_add_one
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {A₁ S₁ T₁ : σ → Rat} {A₂ S₂ T₂ : τ → Rat} {q₁ q₂ : Rat}
    (h₁ : TokenomicsControllerGuard M₁ A₁ S₁ T₁ q₁)
    (h₂ : TokenomicsControllerGuard M₂ A₂ S₂ T₂ q₂)
    (hq₁LeOne : q₁ ≤ 1) (hq₂LeOne : q₂ ≤ 1) :
    TokenomicsControllerGuard
      (asyncProduct M₁ M₂)
      (fun s : σ × τ => A₁ s.1 + A₂ s.2)
      (fun s : σ × τ => S₁ s.1 + S₂ s.2)
      (fun s : σ × τ => T₁ s.1 + T₂ s.2)
      1 where
  supplyFactor := by
    intro s t hStep
    rcases hStep with hLeft | hRight
    · have hSupply := h₁.stepSupplyNonincreasing hq₁LeOne hLeft.1
      change S₁ t.1 + S₂ t.2 ≤ 1 * (S₁ s.1 + S₂ s.2)
      rw [hLeft.2]
      linarith
    · have hSupply := h₂.stepSupplyNonincreasing hq₂LeOne hRight.2
      change S₁ t.1 + S₂ t.2 ≤ 1 * (S₁ s.1 + S₂ s.2)
      rw [hRight.1]
      linarith
  burnFunded := by
    intro s t hStep
    rcases hStep with hLeft | hRight
    · have hFund := h₁.burnFunded hLeft.1
      change
        (S₁ s.1 + S₂ s.2) - (S₁ t.1 + S₂ t.2) ≤
          (T₁ s.1 + T₂ s.2) - (T₁ t.1 + T₂ t.2)
      rw [hLeft.2]
      linarith
    · have hFund := h₂.burnFunded hRight.2
      change
        (S₁ s.1 + S₂ s.2) - (S₁ t.1 + S₂ t.2) ≤
          (T₁ s.1 + T₂ s.2) - (T₁ t.1 + T₂ t.2)
      rw [hRight.1]
      linarith
  outputNondecreasing := by
    intro s t hStep
    rcases hStep with hLeft | hRight
    · change A₁ s.1 + A₂ s.2 ≤ A₁ t.1 + A₂ t.2
      rw [hLeft.2]
      exact add_le_add (h₁.outputNondecreasing hLeft.1) le_rfl
    · change A₁ s.1 + A₂ s.2 ≤ A₁ t.1 + A₂ t.2
      rw [hRight.1]
      exact add_le_add le_rfl (h₂.outputNondecreasing hRight.2)
  treasuryNonnegative := by
    intro s
    exact add_nonneg (h₁.treasuryNonnegative s.1) (h₂.treasuryNonnegative s.2)
  outputNonnegative := by
    intro s
    exact add_nonneg (h₁.outputNonnegative s.1) (h₂.outputNonnegative s.2)
  supplyPositive := by
    intro s
    exact add_pos (h₁.supplyPositive s.1) (h₂.supplyPositive s.2)

end TokenomicsControllerGuard

end MarketSystem

end DeFi

end LeanMathlib
