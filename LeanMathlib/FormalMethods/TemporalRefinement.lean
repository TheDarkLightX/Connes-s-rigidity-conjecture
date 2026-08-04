import LeanMathlib.FormalMethods.TransitionBarrier

namespace LeanMathlib

namespace FormalMethods

namespace TransitionSystem

variable {σ τ α : Type*}

def Refines (impl : TransitionSystem σ) (spec : TransitionSystem τ)
    (view : σ → τ) : Prop :=
  ∀ {s t : σ}, impl.Step s t → spec.Step (view s) (view t)

theorem reachable_view_of_refines {impl : TransitionSystem σ}
    {spec : TransitionSystem τ} {view : σ → τ}
    (hRef : Refines impl spec view)
    {s t : σ} (hReach : impl.Reachable s t) :
    spec.Reachable (view s) (view t) := by
  induction hReach with
  | refl =>
      exact Reachable.refl _
  | tail hReach hStep ih =>
      exact Reachable.tail ih (hRef hStep)

theorem traceN_view_of_refines {impl : TransitionSystem σ}
    {spec : TransitionSystem τ} {view : σ → τ}
    (hRef : Refines impl spec view)
    {n : Nat} {s t : σ} (hTrace : impl.TraceN n s t) :
    spec.TraceN n (view s) (view t) := by
  induction hTrace with
  | nil s =>
      exact TraceN.nil _
  | snoc hTrace hStep ih =>
      exact TraceN.snoc ih (hRef hStep)

theorem barrierPreserved_pullback_of_refines [Preorder α]
    {impl : TransitionSystem σ} {spec : TransitionSystem τ}
    {view : σ → τ} {score : τ → α} {cutoff : α}
    (hRef : Refines impl spec view)
    (hBarrier : spec.BarrierPreserved score cutoff) :
    impl.BarrierPreserved (fun s => score (view s)) cutoff := by
  intro s t hStep hInit
  exact hBarrier (hRef hStep) hInit

theorem safe_of_refined_reachable [Preorder α]
    {impl : TransitionSystem σ} {spec : TransitionSystem τ}
    {view : σ → τ} {safeImpl : σ → Prop} {safeSpec : τ → Prop}
    {score : τ → α} {cutoff : α}
    (hRef : Refines impl spec view)
    (hBarrier : spec.BarrierPreserved score cutoff)
    (hSound : BarrierSound safeSpec score cutoff)
    (hViewSafe : ∀ {s : σ}, safeSpec (view s) → safeImpl s)
    {s t : σ} (hReach : impl.Reachable s t)
    (hInit : cutoff ≤ score (view s)) :
    safeImpl t :=
  hViewSafe
    (safe_of_reachable_barrier hBarrier hSound
      (reachable_view_of_refines hRef hReach) hInit)

theorem safe_of_refined_traceN [Preorder α]
    {impl : TransitionSystem σ} {spec : TransitionSystem τ}
    {view : σ → τ} {safeImpl : σ → Prop} {safeSpec : τ → Prop}
    {score : τ → α} {cutoff : α}
    (hRef : Refines impl spec view)
    (hBarrier : spec.BarrierPreserved score cutoff)
    (hSound : BarrierSound safeSpec score cutoff)
    (hViewSafe : ∀ {s : σ}, safeSpec (view s) → safeImpl s)
    {n : Nat} {s t : σ} (hTrace : impl.TraceN n s t)
    (hInit : cutoff ≤ score (view s)) :
    safeImpl t :=
  safe_of_refined_reachable hRef hBarrier hSound hViewSafe
    (reachable_of_traceN hTrace) hInit

end TransitionSystem

end FormalMethods

end LeanMathlib
