import LeanMathlib.Order.BooleanModalFrames

namespace LeanMathlib

namespace Relational

variable {α β : Type*}

/-- Forward simulation clause for two transition relations. -/
def Forth (z : α → β → Prop) (r : α → α → Prop) (s : β → β → Prop) : Prop :=
  ∀ ⦃a b a'⦄, z a b → r a a' → ∃ b', s b b' ∧ z a' b'

/-- Backward simulation clause for two transition relations. -/
def Back (z : α → β → Prop) (r : α → α → Prop) (s : β → β → Prop) : Prop :=
  ∀ ⦃a b b'⦄, z a b → s b b' → ∃ a', r a a' ∧ z a' b'

/-- Standard relational bisimulation between two transition systems. -/
def IsBisimulation (z : α → β → Prop) (r : α → α → Prop) (s : β → β → Prop) : Prop :=
  Forth z r s ∧ Back z r s

/-- Valuations on state sets agree across a bisimulation relation. -/
def Respects (z : α → β → Prop) (u : Set α) (v : Set β) : Prop :=
  ∀ ⦃a b⦄, z a b → (a ∈ u ↔ b ∈ v)

theorem respects_symm {z : α → β → Prop} {u : Set α} {v : Set β}
    (h : Respects z u v) :
    ∀ ⦃a b⦄, z a b → (b ∈ v ↔ a ∈ u) := by
  intro a b hz
  exact (h hz).symm

theorem forth_iff_diamond_converse_singleton
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hforth : Forth z r s) {a : α} {b : β} (hz : z a b) :
    ∀ ⦃a' : α⦄, a' ∈ diamond r ({a} : Set α) → ∃ b', b' ∈ diamond s ({b} : Set β) ∧ z a' b' := by
  intro a' ha'
  rcases ha' with ⟨a0, ha0, hra⟩
  have hEq : a0 = a := by simpa using ha0
  subst a0
  rcases hforth hz hra with ⟨b', hsb, hzb⟩
  exact ⟨b', ⟨b, by simp, hsb⟩, hzb⟩

theorem back_iff_diamond_converse_singleton
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hback : Back z r s) {a : α} {b : β} (hz : z a b) :
    ∀ ⦃b' : β⦄, b' ∈ diamond s ({b} : Set β) → ∃ a', a' ∈ diamond r ({a} : Set α) ∧ z a' b' := by
  intro b' hb'
  rcases hb' with ⟨b0, hb0, hsb⟩
  have hEq : b0 = b := by simpa using hb0
  subst b0
  rcases hback hz hsb with ⟨a', hra, hza⟩
  exact ⟨a', ⟨a, by simp, hra⟩, hza⟩

theorem bisimulation_diamond_converse_iff
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s) {u : Set α} {v : Set β}
    (hres : Respects z u v) {a : α} {b : β} (hz : z a b) :
    a ∈ diamond (converse r) u ↔ b ∈ diamond (converse s) v := by
  constructor
  · rintro ⟨a', ha', hra⟩
    rcases hbisim.1 hz hra with ⟨b', hsb, hzb⟩
    exact ⟨b', (hres hzb).1 ha', hsb⟩
  · rintro ⟨b', hb', hsb⟩
    rcases hbisim.2 hz hsb with ⟨a', hra, hza⟩
    exact ⟨a', (hres hza).2 hb', hra⟩

theorem bisimulation_box_converse_iff
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s) {u : Set α} {v : Set β}
    (hres : Respects z u v) {a : α} {b : β} (hz : z a b) :
    a ∈ box (converse r) u ↔ b ∈ box (converse s) v := by
  constructor
  · intro haBox
    rw [mem_box_iff]
    intro b' hsb
    rcases hbisim.2 hz hsb with ⟨a', hra, hza⟩
    exact (hres hza).1 ((mem_box_iff (r := converse r) (s := u) (b := a)).1 haBox a' hra)
  · intro hbBox
    rw [mem_box_iff]
    intro a' hra
    rcases hbisim.1 hz hra with ⟨b', hsb, hzb⟩
    exact (hres hzb).2 ((mem_box_iff (r := converse s) (s := v) (b := b)).1 hbBox b' hsb)

end Relational

end LeanMathlib
