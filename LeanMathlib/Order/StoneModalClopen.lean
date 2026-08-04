import LeanMathlib.Order.BooleanModalFrames
import LeanMathlib.Order.StoneMapTransport

namespace LeanMathlib

open Filter

namespace Stone

variable {α β : Type*}

@[simp] theorem basicClopen_compl (s : Set α) :
    basicClopen sᶜ = (basicClopen s)ᶜ := by
  ext u
  simp [basicClopen, Ultrafilter.compl_mem_iff_notMem]

theorem basicClopen_box_eq_compl_basicClopen_diamond_compl
    (r : α → β → Prop) (s : Set α) :
    basicClopen (Relational.box r s) = (basicClopen (Relational.diamond r sᶜ))ᶜ := by
  rw [Relational.box_eq_compl_diamond_compl, basicClopen_compl]

theorem isClopen_basicClopen_diamond (r : α → β → Prop) (s : Set α) :
    IsClopen (basicClopen (Relational.diamond r s)) :=
  isClopen_basicClopen _

theorem isClopen_basicClopen_box (r : α → β → Prop) (s : Set α) :
    IsClopen (basicClopen (Relational.box r s)) := by
  rw [basicClopen_box_eq_compl_basicClopen_diamond_compl]
  exact (isClopen_basicClopen _).compl

@[simp] theorem principalPoint_mem_basicClopen_diamond_iff
    (r : α → β → Prop) (s : Set α) (b : β) :
    principalPoint b ∈ basicClopen (Relational.diamond r s) ↔
      ∃ a, principalPoint a ∈ basicClopen s ∧ r a b := by
  simp [basicClopen, Relational.mem_diamond_iff]

@[simp] theorem principalPoint_mem_basicClopen_box_iff
    (r : α → β → Prop) (s : Set α) (b : β) :
    principalPoint b ∈ basicClopen (Relational.box r s) ↔
      ∀ a, r a b → principalPoint a ∈ basicClopen s := by
  simp [basicClopen, Relational.mem_box_iff]

@[simp] theorem principalPoint_mem_basicClopen_diamond_singleton_iff
    (r : α → β → Prop) (a : α) (b : β) :
    principalPoint b ∈ basicClopen (Relational.diamond r ({a} : Set α)) ↔ r a b := by
  simp

theorem relation_eq_iff_forall_basicClopen_diamond_singleton_eq
    (r s : α → β → Prop) :
    r = s ↔ ∀ a : α,
      basicClopen (Relational.diamond r ({a} : Set α)) =
        basicClopen (Relational.diamond s ({a} : Set α)) := by
  constructor
  · intro h a
    simp [h]
  · intro h
    funext a
    funext b
    apply propext
    have hclopen := h a
    have hset :
        Relational.diamond r ({a} : Set α) = Relational.diamond s ({a} : Set α) :=
      (basicClopen_eq_iff (s := Relational.diamond r ({a} : Set α))
        (t := Relational.diamond s ({a} : Set α))).1 hclopen
    have hb : b ∈ Relational.diamond r ({a} : Set α) ↔
        b ∈ Relational.diamond s ({a} : Set α) := by
      simp [hset]
    simpa [Relational.diamond_singleton] using hb

theorem relation_eq_iff_forall_principalPoint_diamond_singleton_mem
    (r s : α → β → Prop) :
    r = s ↔ ∀ a : α, ∀ b : β,
      (principalPoint b ∈ basicClopen (Relational.diamond r ({a} : Set α)) ↔
        principalPoint b ∈ basicClopen (Relational.diamond s ({a} : Set α))) := by
  constructor
  · intro h a b
    simp [h]
  · intro h
    funext a
    funext b
    apply propext
    simpa using h a b

end Stone

end LeanMathlib
