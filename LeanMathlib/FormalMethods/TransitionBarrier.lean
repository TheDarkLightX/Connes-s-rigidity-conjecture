import Mathlib

namespace LeanMathlib

namespace FormalMethods

structure TransitionSystem (σ : Type*) where
  Step : σ → σ → Prop

namespace TransitionSystem

variable {σ τ α β : Type*}

inductive Reachable (T : TransitionSystem σ) : σ → σ → Prop
  | refl (s : σ) : Reachable T s s
  | tail {s t u : σ} : Reachable T s t → T.Step t u → Reachable T s u

inductive TraceN (T : TransitionSystem σ) : Nat → σ → σ → Prop
  | nil (s : σ) : TraceN T 0 s s
  | snoc {n : Nat} {s t u : σ} :
      TraceN T n s t → T.Step t u → TraceN T (n + 1) s u

def StepIncluded (S T : TransitionSystem σ) : Prop :=
  ∀ {s t : σ}, S.Step s t → T.Step s t

def BarrierPreserved [Preorder α] (T : TransitionSystem σ)
    (score : σ → α) (cutoff : α) : Prop :=
  ∀ {s t : σ}, T.Step s t → cutoff ≤ score s → cutoff ≤ score t

def BarrierSound [Preorder α] (safe : σ → Prop)
    (score : σ → α) (cutoff : α) : Prop :=
  ∀ {s : σ}, cutoff ≤ score s → safe s

structure BarrierCertificate (T : TransitionSystem σ) (safe : σ → Prop)
    (α : Type*) [Preorder α] where
  score : σ → α
  cutoff : α
  step_ok : T.BarrierPreserved score cutoff
  sound : BarrierSound safe score cutoff

def SyncProduct (S : TransitionSystem σ) (T : TransitionSystem τ) :
    TransitionSystem (σ × τ) where
  Step p q := S.Step p.1 q.1 ∧ T.Step p.2 q.2

theorem reachable_of_traceN {T : TransitionSystem σ}
    {n : Nat} {s t : σ} (hTrace : TraceN T n s t) :
    Reachable T s t := by
  induction hTrace with
  | nil s =>
      exact Reachable.refl s
  | snoc hTrace hStep ih =>
      exact Reachable.tail ih hStep

theorem barrier_of_reachable [Preorder α] {T : TransitionSystem σ}
    {score : σ → α} {cutoff : α}
    (hStep : T.BarrierPreserved score cutoff)
    {s t : σ} (hReach : Reachable T s t)
    (hInit : cutoff ≤ score s) :
    cutoff ≤ score t := by
  induction hReach with
  | refl =>
      exact hInit
  | tail hReach hStepOne ih =>
      exact hStep hStepOne ih

theorem barrier_of_traceN [Preorder α] {T : TransitionSystem σ}
    {score : σ → α} {cutoff : α}
    (hStep : T.BarrierPreserved score cutoff)
    {n : Nat} {s t : σ} (hTrace : TraceN T n s t)
    (hInit : cutoff ≤ score s) :
    cutoff ≤ score t :=
  barrier_of_reachable hStep (reachable_of_traceN hTrace) hInit

theorem safe_of_reachable_barrier [Preorder α] {T : TransitionSystem σ}
    {safe : σ → Prop} {score : σ → α} {cutoff : α}
    (hStep : T.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe score cutoff)
    {s t : σ} (hReach : Reachable T s t)
    (hInit : cutoff ≤ score s) :
    safe t :=
  hSound (barrier_of_reachable hStep hReach hInit)

theorem safe_of_traceN_barrier [Preorder α] {T : TransitionSystem σ}
    {safe : σ → Prop} {score : σ → α} {cutoff : α}
    (hStep : T.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe score cutoff)
    {n : Nat} {s t : σ} (hTrace : TraceN T n s t)
    (hInit : cutoff ≤ score s) :
    safe t :=
  safe_of_reachable_barrier hStep hSound (reachable_of_traceN hTrace) hInit

theorem barrierPreserved_of_stepIncluded [Preorder α]
    {S T : TransitionSystem σ} {score : σ → α} {cutoff : α}
    (hInc : StepIncluded S T)
    (hBarrier : T.BarrierPreserved score cutoff) :
    S.BarrierPreserved score cutoff := by
  intro s t hStep hInit
  exact hBarrier (hInc hStep) hInit

theorem pair_barrier_of_sync_reachable [Preorder α] [Preorder β]
    {S : TransitionSystem σ} {T : TransitionSystem τ}
    {scoreS : σ → α} {cutoffS : α}
    {scoreT : τ → β} {cutoffT : β}
    (hS : S.BarrierPreserved scoreS cutoffS)
    (hT : T.BarrierPreserved scoreT cutoffT)
    {p q : σ × τ} (hReach : Reachable (SyncProduct S T) p q)
    (hInit : cutoffS ≤ scoreS p.1 ∧ cutoffT ≤ scoreT p.2) :
    cutoffS ≤ scoreS q.1 ∧ cutoffT ≤ scoreT q.2 := by
  induction hReach with
  | refl =>
      exact hInit
  | tail hReach hStep ih =>
      exact ⟨hS hStep.1 ih.1, hT hStep.2 ih.2⟩

theorem pair_safe_of_sync_reachable [Preorder α] [Preorder β]
    {S : TransitionSystem σ} {T : TransitionSystem τ}
    {safeS : σ → Prop} {safeT : τ → Prop}
    {scoreS : σ → α} {cutoffS : α}
    {scoreT : τ → β} {cutoffT : β}
    (hS : S.BarrierPreserved scoreS cutoffS)
    (hT : T.BarrierPreserved scoreT cutoffT)
    (hSoundS : BarrierSound safeS scoreS cutoffS)
    (hSoundT : BarrierSound safeT scoreT cutoffT)
    {p q : σ × τ} (hReach : Reachable (SyncProduct S T) p q)
    (hInit : cutoffS ≤ scoreS p.1 ∧ cutoffT ≤ scoreT p.2) :
    safeS q.1 ∧ safeT q.2 := by
  have hPair :=
    pair_barrier_of_sync_reachable hS hT hReach hInit
  exact ⟨hSoundS hPair.1, hSoundT hPair.2⟩

namespace BarrierCertificate

variable [Preorder α] {T : TransitionSystem σ} {safe : σ → Prop}

theorem barrier_of_reachable (cert : BarrierCertificate T safe α)
    {s t : σ} (hReach : T.Reachable s t)
    (hInit : cert.cutoff ≤ cert.score s) :
    cert.cutoff ≤ cert.score t :=
  TransitionSystem.barrier_of_reachable cert.step_ok hReach hInit

theorem safe_of_reachable (cert : BarrierCertificate T safe α)
    {s t : σ} (hReach : T.Reachable s t)
    (hInit : cert.cutoff ≤ cert.score s) :
    safe t :=
  cert.sound (cert.barrier_of_reachable hReach hInit)

theorem safe_of_traceN (cert : BarrierCertificate T safe α)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hInit : cert.cutoff ≤ cert.score s) :
    safe t :=
  cert.safe_of_reachable (TransitionSystem.reachable_of_traceN hTrace) hInit

end BarrierCertificate

end TransitionSystem

end FormalMethods

end LeanMathlib
