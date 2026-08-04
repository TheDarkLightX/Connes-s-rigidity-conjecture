import LeanMathlib.DeFi.TraceValueBounds

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

/-- A length-indexed finite market execution. -/
inductive TraceN (M : MarketSystem σ) : Nat → σ → σ → Prop
  | nil (s : σ) : TraceN M 0 s s
  | snoc {n : Nat} {s t u : σ} :
      TraceN M n s t → M.Step t u → TraceN M (n + 1) s u

namespace TraceN

theorem toTrace {M : MarketSystem σ} {n : Nat} {s t : σ}
    (hTrace : TraceN M n s t) :
    Trace M s t := by
  induction hTrace with
  | nil =>
      exact Trace.nil _
  | snoc hTrace hStep ih =>
      exact Trace.snoc ih hStep

theorem mono {M N : MarketSystem σ} {n : Nat}
    (hInc : StepIncluded M N) {s t : σ}
    (hTrace : TraceN M n s t) :
    TraceN N n s t := by
  induction hTrace with
  | nil =>
      exact TraceN.nil _
  | snoc hTrace hStep ih =>
      exact TraceN.snoc ih (hInc hStep)

end TraceN

/-- Every tokenomics step leaves total supply unchanged or lower. -/
def StepSupplyNonincreasing (M : MarketSystem σ) (S : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S t ≤ S s

/-- Every tokenomics step leaves supply at most a fixed factor of the prior supply. -/
def StepSupplyLeFactor (M : MarketSystem σ) (S : σ → Rat) (q : Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → S t ≤ q * S s

/-- Terminal supply removed over a certified length-indexed trace. -/
def traceSupplyDrop {M : MarketSystem σ} (S : σ → Rat)
    {n : Nat} {s t : σ} (_hTrace : TraceN M n s t) : Rat :=
  S s - S t

theorem supply_le_of_traceN_stepSupplyNonincreasing
    (M : MarketSystem σ) (S : σ → Rat)
    (hSupply : StepSupplyNonincreasing M S)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ S s := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact (hSupply hStep).trans ih

theorem traceSupplyDrop_nonneg_of_stepSupplyNonincreasing
    (M : MarketSystem σ) (S : σ → Rat)
    (hSupply : StepSupplyNonincreasing M S)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceSupplyDrop S hTrace := by
  have hLe := supply_le_of_traceN_stepSupplyNonincreasing M S hSupply hTrace
  unfold traceSupplyDrop
  exact sub_nonneg.mpr hLe

theorem factor_pow_le_one
    {q : Rat} (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (n : Nat) :
    q ^ n ≤ 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        q ^ (n + 1) = q ^ n * q := by rw [pow_succ]
        _ ≤ 1 * 1 := mul_le_mul ih hqLeOne hqNonneg (by norm_num)
        _ = 1 := by norm_num

theorem factor_pow_mul_le_initial
    {q initial : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hInitial : 0 ≤ initial)
    (n : Nat) :
    q ^ n * initial ≤ initial := by
  have hPow : q ^ n ≤ 1 := factor_pow_le_one hqNonneg hqLeOne n
  calc
    q ^ n * initial ≤ 1 * initial := mul_le_mul_of_nonneg_right hPow hInitial
    _ = initial := by ring

theorem supply_le_factor_pow_of_traceN
    (M : MarketSystem σ) (S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q)
    (hFactor : StepSupplyLeFactor M S q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    S t ≤ q ^ n * S s := by
  induction hTrace with
  | nil =>
      simp
  | snoc hTrace hStep ih =>
      calc
        S _ ≤ q * S _ := hFactor hStep
        _ ≤ q * (q ^ _ * S _) := mul_le_mul_of_nonneg_left ih hqNonneg
        _ = q ^ (_ + 1) * S _ := by
          rw [pow_succ]
          ring

theorem supply_le_initial_of_traceN_factor
    (M : MarketSystem σ) (S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hFactor : StepSupplyLeFactor M S q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : 0 ≤ S s) :
    S t ≤ S s :=
  (supply_le_factor_pow_of_traceN M S hqNonneg hFactor hTrace).trans
    (factor_pow_mul_le_initial hqNonneg hqLeOne hInitial n)

theorem traceSupplyDrop_nonneg_of_traceN_factor
    (M : MarketSystem σ) (S : σ → Rat) {q : Rat}
    (hqNonneg : 0 ≤ q) (hqLeOne : q ≤ 1)
    (hFactor : StepSupplyLeFactor M S q)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : 0 ≤ S s) :
    0 ≤ traceSupplyDrop S hTrace := by
  have hLe :=
    supply_le_initial_of_traceN_factor
      M S hqNonneg hqLeOne hFactor hTrace hInitial
  unfold traceSupplyDrop
  exact sub_nonneg.mpr hLe

end MarketSystem

end DeFi

end LeanMathlib
