import LeanMathlib.DeFi.LiquidationCaps
import LeanMathlib.DeFi.TokenomicsSupply

namespace LeanMathlib

namespace DeFi

namespace MarketSystem

variable {σ : Type*}

def StepAdverseSolventPreserved
    (M : MarketSystem σ)
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds) : Prop :=
  ∀ {s t : σ}, M.Step s t →
    solventAt (position s) (adversePrice (bounds s)) →
    solventAt (position t) (adversePrice (bounds t))

theorem adverseSolvent_of_traceN
    (M : MarketSystem σ)
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds)
    (hStep : StepAdverseSolventPreserved M position bounds)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : solventAt (position s) (adversePrice (bounds s))) :
    solventAt (position t) (adversePrice (bounds t)) := by
  induction hTrace with
  | nil =>
      exact hInitial
  | snoc hTrace hStepOne ih =>
      exact hStep hStepOne (ih hInitial)

theorem actualSolvent_of_traceN_oracleEnvelope
    (M : MarketSystem σ)
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds)
    (actualPrice : σ → Rat)
    (hStep : StepAdverseSolventPreserved M position bounds)
    (hCollateral : ∀ x : σ, 0 ≤ (position x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : solventAt (position s) (adversePrice (bounds s)))
    (hEnvelope : inOracleEnvelope (bounds t) (actualPrice t)) :
    solventAt (position t) (actualPrice t) := by
  have hAdverse :=
    adverseSolvent_of_traceN M position bounds hStep hTrace hInitial
  exact solventAt_of_inOracleEnvelope (position t) (bounds t)
    (hCollateral t) hEnvelope hAdverse

theorem postLiquidationSolvencyMargin_nonneg_of_traceN_oracleEnvelope
    (M : MarketSystem σ)
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds)
    (actualPrice : σ → Rat)
    (transfer : LiquidationTransfer)
    (hStep : StepAdverseSolventPreserved M position bounds)
    (hCollateral : ∀ x : σ, 0 ≤ (position x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : solventAt (position s) (adversePrice (bounds s)))
    (hEnvelope : inOracleEnvelope (bounds t) (actualPrice t))
    (hValueBound :
      transfer.collateralValueTaken ≤
        (position t).liquidationThreshold * transfer.debtRepaid) :
    0 ≤ postLiquidationSolvencyMargin (position t) (actualPrice t) transfer := by
  have hAdverse :=
    adverseSolvent_of_traceN M position bounds hStep hTrace hInitial
  exact postLiquidationSolvencyMargin_nonneg_of_adverseSolvent_inOracleEnvelope
    (position t) (bounds t) transfer (hCollateral t) hEnvelope hAdverse hValueBound

theorem blockedPolicy_postLiquidationSolvencyMargin_nonneg_of_traceN_oracleEnvelope
    (M : MarketSystem σ)
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds)
    (actualPrice : σ → Rat)
    {action : LendingRiskAction}
    (capped uncapped : LiquidationTransfer)
    (hStep : StepAdverseSolventPreserved M position bounds)
    (hCollateral : ∀ x : σ, 0 ≤ (position x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : solventAt (position s) (adversePrice (bounds s)))
    (hEnvelope : inOracleEnvelope (bounds t) (actualPrice t))
    (hBlock : blocksLiquidation action) :
    0 ≤ postLiquidationSolvencyMargin
      (position t) (actualPrice t) (policyTransfer action capped uncapped) := by
  have hActual :=
    actualSolvent_of_traceN_oracleEnvelope
      M position bounds actualPrice hStep hCollateral hTrace hInitial hEnvelope
  have hMargin : 0 ≤ solvencyMargin (position t) (actualPrice t) :=
    (solventAt_iff_nonneg_solvencyMargin (position t) (actualPrice t)).1 hActual
  have hEq :=
    postLiquidationSolvencyMargin_eq_pre_of_blocksLiquidation
      (position t) (actualPrice t) capped uncapped hBlock
  rwa [hEq]

theorem stepAdverseSolventPreserved_of_stepIncluded
    {M N : MarketSystem σ}
    {position : σ → LendingPosition}
    {bounds : σ → OracleBounds}
    (hInc : StepIncluded M N)
    (hStep : StepAdverseSolventPreserved N position bounds) :
    StepAdverseSolventPreserved M position bounds := by
  intro s t hLocal hSolvent
  exact hStep (hInc hLocal) hSolvent

theorem actualSolvent_of_refinedTraceN_oracleEnvelope
    {M N : MarketSystem σ}
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds)
    (actualPrice : σ → Rat)
    (hInc : StepIncluded M N)
    (hStep : StepAdverseSolventPreserved N position bounds)
    (hCollateral : ∀ x : σ, 0 ≤ (position x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : solventAt (position s) (adversePrice (bounds s)))
    (hEnvelope : inOracleEnvelope (bounds t) (actualPrice t)) :
    solventAt (position t) (actualPrice t) :=
  actualSolvent_of_traceN_oracleEnvelope
    N position bounds actualPrice hStep hCollateral
    (TraceN.mono hInc hTrace) hInitial hEnvelope

theorem postLiquidationMargin_nonneg_of_refinedTraceN_oracleEnvelope
    {M N : MarketSystem σ}
    (position : σ → LendingPosition)
    (bounds : σ → OracleBounds)
    (actualPrice : σ → Rat)
    (transfer : LiquidationTransfer)
    (hInc : StepIncluded M N)
    (hStep : StepAdverseSolventPreserved N position bounds)
    (hCollateral : ∀ x : σ, 0 ≤ (position x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial : solventAt (position s) (adversePrice (bounds s)))
    (hEnvelope : inOracleEnvelope (bounds t) (actualPrice t))
    (hValueBound :
      transfer.collateralValueTaken ≤
        (position t).liquidationThreshold * transfer.debtRepaid) :
    0 ≤ postLiquidationSolvencyMargin (position t) (actualPrice t) transfer :=
  postLiquidationSolvencyMargin_nonneg_of_traceN_oracleEnvelope
    N position bounds actualPrice transfer hStep hCollateral
    (TraceN.mono hInc hTrace) hInitial hEnvelope hValueBound

theorem actualSolvent_pair_of_traceN_oracleEnvelope
    (M : MarketSystem σ)
    (position₁ position₂ : σ → LendingPosition)
    (bounds₁ bounds₂ : σ → OracleBounds)
    (actualPrice₁ actualPrice₂ : σ → Rat)
    (hStep₁ : StepAdverseSolventPreserved M position₁ bounds₁)
    (hStep₂ : StepAdverseSolventPreserved M position₂ bounds₂)
    (hCollateral₁ : ∀ x : σ, 0 ≤ (position₁ x).collateral)
    (hCollateral₂ : ∀ x : σ, 0 ≤ (position₂ x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial₁ : solventAt (position₁ s) (adversePrice (bounds₁ s)))
    (hInitial₂ : solventAt (position₂ s) (adversePrice (bounds₂ s)))
    (hEnvelope₁ : inOracleEnvelope (bounds₁ t) (actualPrice₁ t))
    (hEnvelope₂ : inOracleEnvelope (bounds₂ t) (actualPrice₂ t)) :
    solventAt (position₁ t) (actualPrice₁ t) ∧
      solventAt (position₂ t) (actualPrice₂ t) :=
  ⟨actualSolvent_of_traceN_oracleEnvelope
      M position₁ bounds₁ actualPrice₁ hStep₁ hCollateral₁
      hTrace hInitial₁ hEnvelope₁,
    actualSolvent_of_traceN_oracleEnvelope
      M position₂ bounds₂ actualPrice₂ hStep₂ hCollateral₂
      hTrace hInitial₂ hEnvelope₂⟩

theorem postLiquidationMargin_pair_nonneg_of_traceN_oracleEnvelope
    (M : MarketSystem σ)
    (position₁ position₂ : σ → LendingPosition)
    (bounds₁ bounds₂ : σ → OracleBounds)
    (actualPrice₁ actualPrice₂ : σ → Rat)
    (transfer₁ transfer₂ : LiquidationTransfer)
    (hStep₁ : StepAdverseSolventPreserved M position₁ bounds₁)
    (hStep₂ : StepAdverseSolventPreserved M position₂ bounds₂)
    (hCollateral₁ : ∀ x : σ, 0 ≤ (position₁ x).collateral)
    (hCollateral₂ : ∀ x : σ, 0 ≤ (position₂ x).collateral)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hInitial₁ : solventAt (position₁ s) (adversePrice (bounds₁ s)))
    (hInitial₂ : solventAt (position₂ s) (adversePrice (bounds₂ s)))
    (hEnvelope₁ : inOracleEnvelope (bounds₁ t) (actualPrice₁ t))
    (hEnvelope₂ : inOracleEnvelope (bounds₂ t) (actualPrice₂ t))
    (hValueBound₁ :
      transfer₁.collateralValueTaken ≤
        (position₁ t).liquidationThreshold * transfer₁.debtRepaid)
    (hValueBound₂ :
      transfer₂.collateralValueTaken ≤
        (position₂ t).liquidationThreshold * transfer₂.debtRepaid) :
    0 ≤ postLiquidationSolvencyMargin
      (position₁ t) (actualPrice₁ t) transfer₁ ∧
    0 ≤ postLiquidationSolvencyMargin
      (position₂ t) (actualPrice₂ t) transfer₂ :=
  ⟨postLiquidationSolvencyMargin_nonneg_of_traceN_oracleEnvelope
      M position₁ bounds₁ actualPrice₁ transfer₁ hStep₁ hCollateral₁
      hTrace hInitial₁ hEnvelope₁ hValueBound₁,
    postLiquidationSolvencyMargin_nonneg_of_traceN_oracleEnvelope
      M position₂ bounds₂ actualPrice₂ transfer₂ hStep₂ hCollateral₂
      hTrace hInitial₂ hEnvelope₂ hValueBound₂⟩

end MarketSystem

end DeFi

end LeanMathlib
