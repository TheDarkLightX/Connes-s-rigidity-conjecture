import LeanMathlib.FormalMethods.TransitionBarrier

namespace LeanMathlib

namespace DeFi

namespace AgentIntent

open FormalMethods

variable {σ : Type*}

def NoOverspend (spent budget : σ → Rat) (s : σ) : Prop :=
  spent s ≤ budget s

def StepNoOverspendPreserved
    (T : TransitionSystem σ) (spent budget : σ → Rat) : Prop :=
  ∀ {s t : σ}, T.Step s t → NoOverspend spent budget s →
    NoOverspend spent budget t

def StepSpendRequiresIntent
    (T : TransitionSystem σ) (validIntent : σ → Prop) (spent : σ → Rat) : Prop :=
  ∀ {s t : σ}, T.Step s t → spent s < spent t → validIntent s

structure IntentSettlementCertificate
    (T : TransitionSystem σ) (validIntent : σ → Prop)
    (spent budget : σ → Rat) : Prop where
  noOverspendStep : StepNoOverspendPreserved T spent budget
  spendRequiresIntent : StepSpendRequiresIntent T validIntent spent

theorem noOverspend_of_traceN
    {T : TransitionSystem σ} {spent budget : σ → Rat}
    (hStep : StepNoOverspendPreserved T spent budget)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hInitial : NoOverspend spent budget s) :
    NoOverspend spent budget t := by
  induction hTrace with
  | nil =>
      exact hInitial
  | snoc hTrace hStepOne ih =>
      exact hStep hStepOne (ih hInitial)

theorem noOverspend_of_intentSettlementCertificate
    {T : TransitionSystem σ} {validIntent : σ → Prop}
    {spent budget : σ → Rat}
    (cert : IntentSettlementCertificate T validIntent spent budget)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hInitial : NoOverspend spent budget s) :
    NoOverspend spent budget t :=
  noOverspend_of_traceN cert.noOverspendStep hTrace hInitial

theorem validIntent_of_spending_step
    {T : TransitionSystem σ} {validIntent : σ → Prop}
    {spent budget : σ → Rat}
    (cert : IntentSettlementCertificate T validIntent spent budget)
    {s t : σ} (hStep : T.Step s t)
    (hSpend : spent s < spent t) :
    validIntent s :=
  cert.spendRequiresIntent hStep hSpend

theorem exists_spending_step_of_trace_spend_increase
    {T : TransitionSystem σ} {spent : σ → Rat}
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hIncrease : spent s < spent t) :
    ∃ u v : σ, T.Step u v ∧ spent u < spent v := by
  induction hTrace with
  | nil s =>
      exact False.elim ((lt_irrefl (spent s)) hIncrease)
  | @snoc n s t u hTrace hStep ih =>
      by_cases hLast : spent t < spent u
      · exact ⟨_, _, hStep, hLast⟩
      · have hPrefix : spent s < spent t := by
          exact lt_of_lt_of_le hIncrease (le_of_not_gt hLast)
        exact ih hPrefix

theorem exists_validIntent_spending_step_of_trace_spend_increase
    {T : TransitionSystem σ} {validIntent : σ → Prop}
    {spent budget : σ → Rat}
    (cert : IntentSettlementCertificate T validIntent spent budget)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hIncrease : spent s < spent t) :
    ∃ u v : σ, T.Step u v ∧ validIntent u ∧ spent u < spent v := by
  rcases exists_spending_step_of_trace_spend_increase hTrace hIncrease with
    ⟨u, v, hStep, hSpend⟩
  exact ⟨u, v, hStep, cert.spendRequiresIntent hStep hSpend, hSpend⟩

theorem no_terminal_spend_increase_without_validIntent_step
    {T : TransitionSystem σ} {validIntent : σ → Prop}
    {spent budget : σ → Rat}
    (cert : IntentSettlementCertificate T validIntent spent budget)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hNoAuthorized :
      ∀ {u v : σ}, T.Step u v → validIntent u → ¬ spent u < spent v) :
    ¬ spent s < spent t := by
  intro hIncrease
  rcases exists_validIntent_spending_step_of_trace_spend_increase
      cert hTrace hIncrease with
    ⟨u, v, hStep, hIntent, hSpend⟩
  exact hNoAuthorized hStep hIntent hSpend

theorem traceN_mono_of_stepIncluded
    {S T : TransitionSystem σ}
    (hInc : TransitionSystem.StepIncluded S T)
    {n : Nat} {s t : σ} (hTrace : S.TraceN n s t) :
    T.TraceN n s t := by
  induction hTrace with
  | nil s =>
      exact TransitionSystem.TraceN.nil s
  | snoc hTrace hStep ih =>
      exact TransitionSystem.TraceN.snoc ih (hInc hStep)

theorem stepNoOverspendPreserved_of_stepIncluded
    {S T : TransitionSystem σ} {spent budget : σ → Rat}
    (hInc : TransitionSystem.StepIncluded S T)
    (hPres : StepNoOverspendPreserved T spent budget) :
    StepNoOverspendPreserved S spent budget := by
  intro s t hStep hNo
  exact hPres (hInc hStep) hNo

theorem stepSpendRequiresIntent_of_stepIncluded
    {S T : TransitionSystem σ} {validIntent : σ → Prop} {spent : σ → Rat}
    (hInc : TransitionSystem.StepIncluded S T)
    (hIntent : StepSpendRequiresIntent T validIntent spent) :
    StepSpendRequiresIntent S validIntent spent := by
  intro s t hStep hSpend
  exact hIntent (hInc hStep) hSpend

theorem intentSettlementCertificate_of_stepIncluded
    {S T : TransitionSystem σ} {validIntent : σ → Prop}
    {spent budget : σ → Rat}
    (hInc : TransitionSystem.StepIncluded S T)
    (cert : IntentSettlementCertificate T validIntent spent budget) :
    IntentSettlementCertificate S validIntent spent budget where
  noOverspendStep :=
    stepNoOverspendPreserved_of_stepIncluded hInc cert.noOverspendStep
  spendRequiresIntent :=
    stepSpendRequiresIntent_of_stepIncluded hInc cert.spendRequiresIntent

theorem noOverspend_of_refined_intentSettlementCertificate
    {S T : TransitionSystem σ} {validIntent : σ → Prop}
    {spent budget : σ → Rat}
    (hInc : TransitionSystem.StepIncluded S T)
    (cert : IntentSettlementCertificate T validIntent spent budget)
    {n : Nat} {s t : σ} (hTrace : S.TraceN n s t)
    (hInitial : NoOverspend spent budget s) :
    NoOverspend spent budget t :=
  noOverspend_of_intentSettlementCertificate
    (intentSettlementCertificate_of_stepIncluded hInc cert) hTrace hInitial

def JointNoOverspend
    (spent₁ budget₁ spent₂ budget₂ : σ → Rat) (s : σ) : Prop :=
  NoOverspend spent₁ budget₁ s ∧ NoOverspend spent₂ budget₂ s

structure JointIntentSettlementCertificate
    (T : TransitionSystem σ) (validIntent₁ validIntent₂ : σ → Prop)
    (spent₁ budget₁ spent₂ budget₂ : σ → Rat) : Prop where
  left : IntentSettlementCertificate T validIntent₁ spent₁ budget₁
  right : IntentSettlementCertificate T validIntent₂ spent₂ budget₂

theorem jointNoOverspend_of_traceN
    {T : TransitionSystem σ} {validIntent₁ validIntent₂ : σ → Prop}
    {spent₁ budget₁ spent₂ budget₂ : σ → Rat}
    (cert :
      JointIntentSettlementCertificate T validIntent₁ validIntent₂
        spent₁ budget₁ spent₂ budget₂)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hInitial : JointNoOverspend spent₁ budget₁ spent₂ budget₂ s) :
    JointNoOverspend spent₁ budget₁ spent₂ budget₂ t :=
  ⟨noOverspend_of_intentSettlementCertificate cert.left hTrace hInitial.1,
    noOverspend_of_intentSettlementCertificate cert.right hTrace hInitial.2⟩

theorem stepSpendRequiresIntent_add
    {T : TransitionSystem σ} {validIntent₁ validIntent₂ : σ → Prop}
    {spent₁ spent₂ : σ → Rat}
    (h₁ : StepSpendRequiresIntent T validIntent₁ spent₁)
    (h₂ : StepSpendRequiresIntent T validIntent₂ spent₂) :
    StepSpendRequiresIntent T
      (fun s => validIntent₁ s ∨ validIntent₂ s)
      (fun s => spent₁ s + spent₂ s) := by
  intro s t hStep hSpend
  by_cases hLeft : spent₁ s < spent₁ t
  · exact Or.inl (h₁ hStep hLeft)
  · have hRight : spent₂ s < spent₂ t := by
      linarith [le_of_not_gt hLeft]
    exact Or.inr (h₂ hStep hRight)

theorem validIntent_or_of_total_spending_step
    {T : TransitionSystem σ} {validIntent₁ validIntent₂ : σ → Prop}
    {spent₁ budget₁ spent₂ budget₂ : σ → Rat}
    (cert :
      JointIntentSettlementCertificate T validIntent₁ validIntent₂
        spent₁ budget₁ spent₂ budget₂)
    {s t : σ} (hStep : T.Step s t)
    (hSpend : spent₁ s + spent₂ s < spent₁ t + spent₂ t) :
    validIntent₁ s ∨ validIntent₂ s :=
  stepSpendRequiresIntent_add
    cert.left.spendRequiresIntent cert.right.spendRequiresIntent hStep hSpend

theorem exists_validIntent_or_step_of_trace_total_spend_increase
    {T : TransitionSystem σ} {validIntent₁ validIntent₂ : σ → Prop}
    {spent₁ budget₁ spent₂ budget₂ : σ → Rat}
    (cert :
      JointIntentSettlementCertificate T validIntent₁ validIntent₂
        spent₁ budget₁ spent₂ budget₂)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hIncrease : spent₁ s + spent₂ s < spent₁ t + spent₂ t) :
    ∃ u v : σ, T.Step u v ∧
      (validIntent₁ u ∨ validIntent₂ u) ∧
      spent₁ u + spent₂ u < spent₁ v + spent₂ v := by
  have hTotalIntent :
      StepSpendRequiresIntent T
        (fun x => validIntent₁ x ∨ validIntent₂ x)
        (fun x => spent₁ x + spent₂ x) :=
    stepSpendRequiresIntent_add
      cert.left.spendRequiresIntent cert.right.spendRequiresIntent
  rcases exists_spending_step_of_trace_spend_increase
      (spent := fun x => spent₁ x + spent₂ x) hTrace hIncrease with
    ⟨u, v, hStep, hSpend⟩
  exact ⟨u, v, hStep, hTotalIntent hStep hSpend, hSpend⟩

end AgentIntent

end DeFi

end LeanMathlib
