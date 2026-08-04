import LeanMathlib.Order.BooleanBisimulation

namespace LeanMathlib

namespace Relational

variable {α β σ : Type*}

theorem respects_bot (z : α → β → Prop) : Respects z (∅ : Set α) (∅ : Set β) := by
  intro a b hz
  simp

theorem respects_top (z : α → β → Prop) : Respects z (Set.univ : Set α) (Set.univ : Set β) := by
  intro a b hz
  simp

theorem respects_compl {z : α → β → Prop} {u : Set α} {v : Set β}
    (h : Respects z u v) :
    Respects z uᶜ vᶜ := by
  intro a b hz
  simpa using not_congr (h hz)

theorem respects_union {z : α → β → Prop}
    {u₁ u₂ : Set α} {v₁ v₂ : Set β}
    (h₁ : Respects z u₁ v₁) (h₂ : Respects z u₂ v₂) :
    Respects z (u₁ ∪ u₂) (v₁ ∪ v₂) := by
  intro a b hz
  simp [h₁ hz, h₂ hz]

theorem respects_inter {z : α → β → Prop}
    {u₁ u₂ : Set α} {v₁ v₂ : Set β}
    (h₁ : Respects z u₁ v₁) (h₂ : Respects z u₂ v₂) :
    Respects z (u₁ ∩ u₂) (v₁ ∩ v₂) := by
  intro a b hz
  simp [h₁ hz, h₂ hz]

theorem respects_sdiff {z : α → β → Prop}
    {u₁ u₂ : Set α} {v₁ v₂ : Set β}
    (h₁ : Respects z u₁ v₁) (h₂ : Respects z u₂ v₂) :
    Respects z (u₁ \ u₂) (v₁ \ v₂) := by
  intro a b hz
  simp [Set.mem_diff, h₁ hz, h₂ hz]

theorem respects_diamond_converse
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s) {u : Set α} {v : Set β}
    (hres : Respects z u v) :
    Respects z (diamond (converse r) u) (diamond (converse s) v) := by
  intro a b hz
  exact bisimulation_diamond_converse_iff hbisim hres hz

theorem respects_box_converse
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s) {u : Set α} {v : Set β}
    (hres : Respects z u v) :
    Respects z (box (converse r) u) (box (converse s) v) := by
  intro a b hz
  exact bisimulation_box_converse_iff hbisim hres hz

/-- Finite modal formulas over a family of atomic propositions. -/
inductive ModalFormula (σ : Type*)
  | atom : σ → ModalFormula σ
  | bot : ModalFormula σ
  | compl : ModalFormula σ → ModalFormula σ
  | sup : ModalFormula σ → ModalFormula σ → ModalFormula σ
  | diamond : ModalFormula σ → ModalFormula σ
  deriving Repr

namespace ModalFormula

/-- Derived conjunction. -/
def inf (φ ψ : ModalFormula σ) : ModalFormula σ :=
  compl (sup (compl φ) (compl ψ))

/-- Derived top. -/
def top : ModalFormula σ :=
  compl bot

/-- Derived box modality. -/
def box (φ : ModalFormula σ) : ModalFormula σ :=
  compl (diamond (compl φ))

end ModalFormula

/-- Set-valued semantics for finite modal formulas. -/
def eval (r : α → α → Prop) (ν : σ → Set α) : ModalFormula σ → Set α
  | .atom p => ν p
  | .bot => ∅
  | .compl φ => (eval r ν φ)ᶜ
  | .sup φ ψ => eval r ν φ ∪ eval r ν ψ
  | .diamond φ => diamond (converse r) (eval r ν φ)

/-- Satisfaction relation induced by `eval`. -/
def Satisfies (r : α → α → Prop) (ν : σ → Set α) (a : α) (φ : ModalFormula σ) : Prop :=
  a ∈ eval r ν φ

@[simp] theorem eval_atom (r : α → α → Prop) (ν : σ → Set α) (p : σ) :
    eval r ν (.atom p) = ν p := rfl

@[simp] theorem eval_bot (r : α → α → Prop) (ν : σ → Set α) :
    eval r ν .bot = ∅ := rfl

@[simp] theorem eval_compl (r : α → α → Prop) (ν : σ → Set α) (φ : ModalFormula σ) :
    eval r ν (.compl φ) = (eval r ν φ)ᶜ := rfl

@[simp] theorem eval_sup (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : ModalFormula σ) :
    eval r ν (.sup φ ψ) = eval r ν φ ∪ eval r ν ψ := rfl

@[simp] theorem eval_diamond (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) :
    eval r ν (.diamond φ) = diamond (converse r) (eval r ν φ) := rfl

@[simp] theorem eval_inf (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : ModalFormula σ) :
    eval r ν (ModalFormula.inf φ ψ) = eval r ν φ ∩ eval r ν ψ := by
  ext a
  simp [ModalFormula.inf, eval]

@[simp] theorem eval_top (r : α → α → Prop) (ν : σ → Set α) :
    eval r ν ModalFormula.top = Set.univ := by
  ext a
  simp [ModalFormula.top, eval]

@[simp] theorem eval_box (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) :
    eval r ν (ModalFormula.box φ) = box (converse r) (eval r ν φ) := by
  calc
    eval r ν (ModalFormula.box φ)
        = (diamond (converse r) (eval r ν φ)ᶜ)ᶜ := by
          rfl
    _ = box (converse r) (eval r ν φ) := by
      symm
      exact box_eq_compl_diamond_compl (r := converse r) (s := eval r ν φ)

theorem eval_respects
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s)
    {να : σ → Set α} {νβ : σ → Set β}
    (hval : ∀ p, Respects z (να p) (νβ p)) :
    ∀ φ : ModalFormula σ, Respects z (eval r να φ) (eval s νβ φ)
  | .atom p => hval p
  | .bot => respects_bot z
  | .compl φ => respects_compl (eval_respects hbisim hval φ)
  | .sup φ ψ => respects_union (eval_respects hbisim hval φ) (eval_respects hbisim hval ψ)
  | .diamond φ => respects_diamond_converse hbisim (eval_respects hbisim hval φ)

theorem satisfies_iff_of_bisimulation
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s)
    {να : σ → Set α} {νβ : σ → Set β}
    (hval : ∀ p, Respects z (να p) (νβ p))
    {a : α} {b : β} (hz : z a b) (φ : ModalFormula σ) :
    Satisfies r να a φ ↔ Satisfies s νβ b φ := by
  exact eval_respects hbisim hval φ hz

end Relational

end LeanMathlib
