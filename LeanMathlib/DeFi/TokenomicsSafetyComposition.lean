import LeanMathlib.DeFi.TokenomicsControllerComposition
import LeanMathlib.DeFi.TokenomicsSafetyEnvelope

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ τ : Type*}

/-- A supply floor that holds for every state in the model. -/
def StateSupplyFloor (S : σ → Rat) (floor : Rat) : Prop :=
  ∀ s : σ, floor ≤ S s

theorem stepSupplyFloor_of_stateSupplyFloor
    {M : MarketSystem σ} {S : σ → Rat} {floor : Rat}
    (hFloor : StateSupplyFloor S floor) :
    StepSupplyFloor M S floor := by
  intro s t hStep
  exact hFloor t

theorem product_stateSupplyFloor_add
    {S₁ : σ → Rat} {S₂ : τ → Rat} {floor₁ floor₂ : Rat}
    (hFloor₁ : StateSupplyFloor S₁ floor₁)
    (hFloor₂ : StateSupplyFloor S₂ floor₂) :
    StateSupplyFloor
      (fun s : σ × τ => S₁ s.1 + S₂ s.2)
      (floor₁ + floor₂) := by
  intro s
  exact add_le_add (hFloor₁ s.1) (hFloor₂ s.2)

theorem syncProduct_stepSupplyFloor_add
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {S₁ : σ → Rat} {S₂ : τ → Rat} {floor₁ floor₂ : Rat}
    (hFloor₁ : StepSupplyFloor M₁ S₁ floor₁)
    (hFloor₂ : StepSupplyFloor M₂ S₂ floor₂) :
    StepSupplyFloor
      (syncProduct M₁ M₂)
      (fun s : σ × τ => S₁ s.1 + S₂ s.2)
      (floor₁ + floor₂) := by
  intro s t hStep
  exact add_le_add (hFloor₁ hStep.1) (hFloor₂ hStep.2)

theorem asyncProduct_stepSupplyFloor_add_of_stateFloors
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {S₁ : σ → Rat} {S₂ : τ → Rat} {floor₁ floor₂ : Rat}
    (hFloor₁ : StateSupplyFloor S₁ floor₁)
    (hFloor₂ : StateSupplyFloor S₂ floor₂) :
    StepSupplyFloor
      (asyncProduct M₁ M₂)
      (fun s : σ × τ => S₁ s.1 + S₂ s.2)
      (floor₁ + floor₂) :=
  stepSupplyFloor_of_stateSupplyFloor
    (product_stateSupplyFloor_add hFloor₁ hFloor₂)

theorem syncProduct_controller_trace_safety_envelope_add
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {A₁ S₁ T₁ : σ → Rat} {A₂ S₂ T₂ : τ → Rat}
    {q floor₁ floor₂ : Rat}
    (hGuard₁ : TokenomicsControllerGuard M₁ A₁ S₁ T₁ q)
    (hGuard₂ : TokenomicsControllerGuard M₂ A₂ S₂ T₂ q)
    (hFloor₁ : StepSupplyFloor M₁ S₁ floor₁)
    (hFloor₂ : StepSupplyFloor M₂ S₂ floor₂)
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    {n : Nat} {s t : σ × τ}
    (hTrace : TraceN (syncProduct M₁ M₂) n s t)
    (hFloor₁Nonneg : 0 ≤ floor₁)
    (hFloor₂Nonneg : 0 ≤ floor₂)
    (hInitialFloor : floor₁ + floor₂ ≤ S₁ s.1 + S₂ s.2) :
    floor₁ + floor₂ ≤ S₁ t.1 + S₂ t.2 ∧
      S₁ t.1 + S₂ t.2 ≤ S₁ s.1 + S₂ s.2 ∧
      0 ≤ traceSupplyDrop (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ∧
      traceSupplyDrop (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ≤
        (S₁ s.1 + S₂ s.2) - (floor₁ + floor₂) ∧
      traceSupplyDrop (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ≤
        T₁ s.1 + T₂ s.2 ∧
      outputPerToken
        (fun x : σ × τ => A₁ x.1 + A₂ x.2)
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) s ≤
      outputPerToken
        (fun x : σ × τ => A₁ x.1 + A₂ x.2)
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) t :=
  controller_trace_safety_envelope
    (TokenomicsControllerGuard.syncProduct_add hGuard₁ hGuard₂)
    (syncProduct_stepSupplyFloor_add hFloor₁ hFloor₂)
    hqNonneg hqLeOne hTrace
    (add_nonneg hFloor₁Nonneg hFloor₂Nonneg)
    hInitialFloor

theorem asyncProduct_controller_trace_safety_envelope_add_one
    {M₁ : MarketSystem σ} {M₂ : MarketSystem τ}
    {A₁ S₁ T₁ : σ → Rat} {A₂ S₂ T₂ : τ → Rat}
    {q₁ q₂ floor₁ floor₂ : Rat}
    (hGuard₁ : TokenomicsControllerGuard M₁ A₁ S₁ T₁ q₁)
    (hGuard₂ : TokenomicsControllerGuard M₂ A₂ S₂ T₂ q₂)
    (hFloor₁ : StateSupplyFloor S₁ floor₁)
    (hFloor₂ : StateSupplyFloor S₂ floor₂)
    (hq₁LeOne : q₁ ≤ 1) (hq₂LeOne : q₂ ≤ 1)
    {n : Nat} {s t : σ × τ}
    (hTrace : TraceN (asyncProduct M₁ M₂) n s t)
    (hFloor₁Nonneg : 0 ≤ floor₁)
    (hFloor₂Nonneg : 0 ≤ floor₂) :
    floor₁ + floor₂ ≤ S₁ t.1 + S₂ t.2 ∧
      S₁ t.1 + S₂ t.2 ≤ S₁ s.1 + S₂ s.2 ∧
      0 ≤ traceSupplyDrop (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ∧
      traceSupplyDrop (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ≤
        (S₁ s.1 + S₂ s.2) - (floor₁ + floor₂) ∧
      traceSupplyDrop (fun x : σ × τ => S₁ x.1 + S₂ x.2) hTrace ≤
        T₁ s.1 + T₂ s.2 ∧
      outputPerToken
        (fun x : σ × τ => A₁ x.1 + A₂ x.2)
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) s ≤
      outputPerToken
        (fun x : σ × τ => A₁ x.1 + A₂ x.2)
        (fun x : σ × τ => S₁ x.1 + S₂ x.2) t :=
  controller_trace_safety_envelope
    (TokenomicsControllerGuard.asyncProduct_add_one
      hGuard₁ hGuard₂ hq₁LeOne hq₂LeOne)
    (asyncProduct_stepSupplyFloor_add_of_stateFloors hFloor₁ hFloor₂)
    (by norm_num) le_rfl hTrace
    (add_nonneg hFloor₁Nonneg hFloor₂Nonneg)
    ((product_stateSupplyFloor_add hFloor₁ hFloor₂) s)

end MarketSystem

end DeFi

end LeanMathlib
