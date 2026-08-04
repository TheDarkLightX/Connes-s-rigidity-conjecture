import LeanMathlib.Order.BooleanModalFormulaInvariance

namespace LeanMathlib

namespace Relational

variable {α β γ δ σ : Type*}

def RelComp (z : α → β → Prop) (w : β → γ → Prop) : α → γ → Prop :=
  fun a c => ∃ b, z a b ∧ w b c

def RelFlip (z : α → β → Prop) : β → α → Prop :=
  fun b a => z a b

theorem relComp_assoc
    {z : α → β → Prop} {w : β → γ → Prop} {v : γ → δ → Prop}
    {a : α} {d : δ} :
    RelComp (RelComp z w) v a d ↔ RelComp z (RelComp w v) a d := by
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, ⟨c, hbc, hcd⟩⟩
  · rintro ⟨b, hab, ⟨c, hbc, hcd⟩⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

theorem respects_comp
    {z : α → β → Prop} {w : β → γ → Prop}
    {u : Set α} {v : Set β} {x : Set γ}
    (hz : Respects z u v) (hw : Respects w v x) :
    Respects (RelComp z w) u x := by
  intro a c hRel
  rcases hRel with ⟨b, hab, hbc⟩
  exact (hz hab).trans (hw hbc)

theorem isBisimulation_comp
    {z : α → β → Prop} {w : β → γ → Prop}
    {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (hz : IsBisimulation z r s) (hw : IsBisimulation w s t) :
    IsBisimulation (RelComp z w) r t := by
  constructor
  · intro a c a' hRel hStep
    rcases hRel with ⟨b, hab, hbc⟩
    rcases hz.1 hab hStep with ⟨b', hStepB, hab'⟩
    rcases hw.1 hbc hStepB with ⟨c', hStepC, hbc'⟩
    exact ⟨c', hStepC, ⟨b', hab', hbc'⟩⟩
  · intro a c c' hRel hStep
    rcases hRel with ⟨b, hab, hbc⟩
    rcases hw.2 hbc hStep with ⟨b', hStepB, hbc'⟩
    rcases hz.2 hab hStepB with ⟨a', hStepA, hab'⟩
    exact ⟨a', hStepA, ⟨b', hab', hbc'⟩⟩

theorem respects_eq (u : Set α) :
    Respects (fun a b : α => a = b) u u := by
  intro a b hab
  subst b
  rfl

theorem respects_flip
    {z : α → β → Prop} {u : Set α} {v : Set β}
    (h : Respects z u v) :
    Respects (RelFlip z) v u := by
  intro b a hRel
  exact (h hRel).symm

theorem isBisimulation_eq (r : α → α → Prop) :
    IsBisimulation (fun a b : α => a = b) r r := by
  constructor
  · intro a b a' hab hStep
    subst b
    exact ⟨a', hStep, rfl⟩
  · intro a b b' hab hStep
    subst b
    exact ⟨b', hStep, rfl⟩

theorem isBisimulation_flip
    {z : α → β → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    (h : IsBisimulation z r s) :
    IsBisimulation (RelFlip z) s r := by
  constructor
  · intro b a b' hRel hStep
    exact h.2 hRel hStep
  · intro b a a' hRel hStep
    exact h.1 hRel hStep

structure ModalProtocolQuotient
    (z : α → β → Prop)
    (r : α → α → Prop) (s : β → β → Prop)
    (να : σ → Set α) (νβ : σ → Set β) : Prop where
  bisim : IsBisimulation z r s
  valuation_respects : ∀ p : σ, Respects z (να p) (νβ p)

namespace ModalProtocolQuotient

theorem satisfies_iff
    {z : α → β → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    (Q : ModalProtocolQuotient z r s να νβ)
    {a : α} {b : β} (hz : z a b) (φ : ModalFormula σ) :
    Satisfies r να a φ ↔ Satisfies s νβ b φ :=
  satisfies_iff_of_bisimulation Q.bisim Q.valuation_respects hz φ

theorem concrete_satisfies_of_abstract
    {z : α → β → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    (Q : ModalProtocolQuotient z r s να νβ)
    {a : α} {b : β} (hz : z a b) (φ : ModalFormula σ)
    (hAbstract : Satisfies s νβ b φ) :
    Satisfies r να a φ :=
  (Q.satisfies_iff hz φ).2 hAbstract

theorem abstract_satisfies_of_concrete
    {z : α → β → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    (Q : ModalProtocolQuotient z r s να νβ)
    {a : α} {b : β} (hz : z a b) (φ : ModalFormula σ)
    (hConcrete : Satisfies r να a φ) :
    Satisfies s νβ b φ :=
  (Q.satisfies_iff hz φ).1 hConcrete

theorem comp
    {z : α → β → Prop} {w : β → γ → Prop}
    {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    {να : σ → Set α} {νβ : σ → Set β} {νγ : σ → Set γ}
    (Q₁ : ModalProtocolQuotient z r s να νβ)
    (Q₂ : ModalProtocolQuotient w s t νβ νγ) :
    ModalProtocolQuotient (RelComp z w) r t να νγ where
  bisim := isBisimulation_comp Q₁.bisim Q₂.bisim
  valuation_respects := by
    intro p
    exact respects_comp (Q₁.valuation_respects p) (Q₂.valuation_respects p)

theorem satisfies_iff_comp
    {z : α → β → Prop} {w : β → γ → Prop}
    {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    {να : σ → Set α} {νβ : σ → Set β} {νγ : σ → Set γ}
    (Q₁ : ModalProtocolQuotient z r s να νβ)
    (Q₂ : ModalProtocolQuotient w s t νβ νγ)
    {a : α} {c : γ} (hRel : RelComp z w a c) (φ : ModalFormula σ) :
    Satisfies r να a φ ↔ Satisfies t νγ c φ :=
  (Q₁.comp Q₂).satisfies_iff hRel φ

theorem comp_three
    {z : α → β → Prop} {w : β → γ → Prop} {v : γ → δ → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} {u : δ → δ → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    {νγ : σ → Set γ} {νδ : σ → Set δ}
    (Q₁ : ModalProtocolQuotient z r s να νβ)
    (Q₂ : ModalProtocolQuotient w s t νβ νγ)
    (Q₃ : ModalProtocolQuotient v t u νγ νδ) :
    ModalProtocolQuotient (RelComp z (RelComp w v)) r u να νδ :=
  Q₁.comp (Q₂.comp Q₃)

theorem satisfies_iff_comp_three
    {z : α → β → Prop} {w : β → γ → Prop} {v : γ → δ → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} {u : δ → δ → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    {νγ : σ → Set γ} {νδ : σ → Set δ}
    (Q₁ : ModalProtocolQuotient z r s να νβ)
    (Q₂ : ModalProtocolQuotient w s t νβ νγ)
    (Q₃ : ModalProtocolQuotient v t u νγ νδ)
    {a : α} {d : δ} (hRel : RelComp z (RelComp w v) a d)
    (φ : ModalFormula σ) :
    Satisfies r να a φ ↔ Satisfies u νδ d φ :=
  (Q₁.comp_three Q₂ Q₃).satisfies_iff hRel φ

theorem refl
    (r : α → α → Prop) (ν : σ → Set α) :
    ModalProtocolQuotient (fun a b : α => a = b) r r ν ν where
  bisim := isBisimulation_eq r
  valuation_respects := by
    intro p
    exact respects_eq (ν p)

theorem symm
    {z : α → β → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    (Q : ModalProtocolQuotient z r s να νβ) :
    ModalProtocolQuotient (RelFlip z) s r νβ να where
  bisim := isBisimulation_flip Q.bisim
  valuation_respects := by
    intro p
    exact respects_flip (Q.valuation_respects p)

theorem satisfies_iff_symm
    {z : α → β → Prop}
    {r : α → α → Prop} {s : β → β → Prop}
    {να : σ → Set α} {νβ : σ → Set β}
    (Q : ModalProtocolQuotient z r s να νβ)
    {a : α} {b : β} (hz : z a b) (φ : ModalFormula σ) :
    Satisfies s νβ b φ ↔ Satisfies r να a φ :=
  Q.symm.satisfies_iff hz φ

end ModalProtocolQuotient

end Relational

end LeanMathlib
