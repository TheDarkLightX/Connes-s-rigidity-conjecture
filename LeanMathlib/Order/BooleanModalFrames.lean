import LeanMathlib.Order.BooleanOperators

namespace LeanMathlib

namespace Relational

variable {α β γ : Type*}

/-- Converse relation. -/
def converse (r : α → β → Prop) : β → α → Prop :=
  fun b a => r a b

/-- Relational composition. -/
def compose (r : α → β → Prop) (s : β → γ → Prop) : α → γ → Prop :=
  fun a c => ∃ b, r a b ∧ s b c

@[simp] theorem converse_converse (r : α → β → Prop) :
    converse (converse r) = r :=
  rfl

/--
Forward modal operator induced by a relation, viewed as a join-preserving
bottom-preserving Boolean operator on powersets.
-/
def diamond (r : α → β → Prop) : SupBotHom (Set α) (Set β) where
  toFun s := { b | ∃ a ∈ s, r a b }
  map_sup' := by
    intro s t
    ext b
    constructor
    · rintro ⟨a, ha, hr⟩
      rcases ha with ha | ha
      · exact Or.inl ⟨a, ha, hr⟩
      · exact Or.inr ⟨a, ha, hr⟩
    · intro hb
      rcases hb with ⟨a, ha, hr⟩ | ⟨a, ha, hr⟩
      · exact ⟨a, Or.inl ha, hr⟩
      · exact ⟨a, Or.inr ha, hr⟩
  map_bot' := by
    ext b
    simp

/--
Backward universal modal operator induced by a relation, as the De Morgan dual
of `diamond`.
-/
def box (r : α → β → Prop) : InfTopHom (Set α) (Set β) :=
  SupBotHom.complDual (diamond r)

@[simp] theorem mem_diamond_iff (r : α → β → Prop) (s : Set α) (b : β) :
    b ∈ diamond r s ↔ ∃ a, a ∈ s ∧ r a b := by
  rfl

@[simp] theorem mem_box_iff (r : α → β → Prop) (s : Set α) (b : β) :
    b ∈ box r s ↔ ∀ a, r a b → a ∈ s := by
  constructor
  · intro hb a hra
    by_contra hnot
    have hmem : b ∈ diamond r sᶜ := ⟨a, hnot, hra⟩
    exact hb hmem
  · intro hb hbad
    rcases hbad with ⟨a, ha, hra⟩
    exact ha (hb a hra)

theorem box_eq_compl_diamond_compl (r : α → β → Prop) (s : Set α) :
    box r s = (diamond r sᶜ)ᶜ :=
  rfl

@[simp] theorem diamond_singleton (r : α → β → Prop) (a : α) :
    diamond r ({a} : Set α) = { b | r a b } := by
  ext b
  simp [diamond]

@[simp] theorem diamond_comp (r : α → β → Prop) (s : β → γ → Prop) :
    diamond (compose r s) = (diamond s).comp (diamond r) := by
  ext u c
  constructor
  · rintro ⟨a, ha, b, hr, hs⟩
    exact ⟨b, ⟨a, ha, hr⟩, hs⟩
  · rintro ⟨b, ⟨a, ha, hr⟩, hs⟩
    exact ⟨a, ha, b, hr, hs⟩

@[simp] theorem box_comp (r : α → β → Prop) (s : β → γ → Prop) :
    box (compose r s) = (box s).comp (box r) := by
  rw [box, box, box, ← SupBotHom.complDual_comp]
  exact congrArg SupBotHom.complDual (diamond_comp (r := r) (s := s))

theorem diamond_le_iff (r : α → β → Prop) (s : Set α) (t : Set β) :
    diamond r s ≤ t ↔ s ≤ box (converse r) t := by
  constructor
  · intro h a ha
    exact (mem_box_iff (r := converse r) (s := t) (b := a)).2
      (fun b hr => h ⟨a, ha, hr⟩)
  · intro h b hb
    rcases hb with ⟨a, ha, hr⟩
    exact (mem_box_iff (r := converse r) (s := t) (b := a)).1 (h ha) b hr

theorem le_box_iff (r : α → β → Prop) (s : Set β) (t : Set α) :
    s ≤ box r t ↔ diamond (converse r) s ≤ t := by
  simpa [converse_converse] using
    (diamond_le_iff (r := converse r) (s := s) (t := t)).symm

end Relational

end LeanMathlib
