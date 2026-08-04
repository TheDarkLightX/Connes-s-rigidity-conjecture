import LeanMathlib.Order.BooleanModalFrames

namespace LeanMathlib

namespace Relational

variable {α β : Type*}

/-- Pointwise inclusion of relations. -/
def Subrelation (r s : α → β → Prop) : Prop :=
  ∀ ⦃a b⦄, r a b → s a b

theorem relation_iff_mem_diamond_singleton (r : α → β → Prop) (a : α) (b : β) :
    r a b ↔ b ∈ diamond r ({a} : Set α) := by
  constructor
  · intro hr
    exact ⟨a, by simp, hr⟩
  · rintro ⟨a', ha', hr⟩
    have ha'' : a' = a := by simpa using ha'
    subst a'
    exact hr

theorem subrelation_iff_forall_singleton_diamond_subset
    (r s : α → β → Prop) :
    Subrelation r s ↔ ∀ a, diamond r ({a} : Set α) ≤ diamond s ({a} : Set α) := by
  constructor
  · intro hrs a b hb
    rcases hb with ⟨a', ha', hr⟩
    exact ⟨a', ha', hrs hr⟩
  · intro hsub a b hr
    have hb : b ∈ diamond r ({a} : Set α) := (relation_iff_mem_diamond_singleton r a b).1 hr
    exact (relation_iff_mem_diamond_singleton s a b).2 (hsub a hb)

theorem subrelation_iff_forall_diamond_subset
    (r s : α → β → Prop) :
    Subrelation r s ↔ ∀ u : Set α, diamond r u ≤ diamond s u := by
  constructor
  · intro hrs u b hb
    rcases hb with ⟨a, ha, hr⟩
    exact ⟨a, ha, hrs hr⟩
  · intro h a b hr
    have hb : b ∈ diamond r ({a} : Set α) := (relation_iff_mem_diamond_singleton r a b).1 hr
    exact (relation_iff_mem_diamond_singleton s a b).2 (h {a} hb)

theorem subrelation_iff_diamond_le (r s : α → β → Prop) :
    Subrelation r s ↔ diamond r ≤ diamond s := by
  constructor
  · intro hrs u
    exact (subrelation_iff_forall_diamond_subset r s).1 hrs u
  · intro h
    exact (subrelation_iff_forall_diamond_subset r s).2 (fun u => h u)

theorem relation_eq_iff_forall_singleton_diamond_eq
    (r s : α → β → Prop) :
    r = s ↔ ∀ a, diamond r ({a} : Set α) = diamond s ({a} : Set α) := by
  constructor
  · intro hrs a
    simp [hrs]
  · intro h
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    rw [relation_iff_mem_diamond_singleton r a b, h a, relation_iff_mem_diamond_singleton s a b]

theorem relation_eq_iff_diamond_eq (r s : α → β → Prop) :
    r = s ↔ diamond r = diamond s := by
  constructor
  · intro hrs
    simp [hrs]
  · intro h
    exact (relation_eq_iff_forall_singleton_diamond_eq r s).2
      (fun a => congrArg (fun f => f ({a} : Set α)) h)

theorem relation_eq_iff_box_eq (r s : α → β → Prop) :
    r = s ↔ box r = box s := by
  constructor
  · intro hrs
    simp [hrs]
  · intro h
    have hdiamond : diamond r = diamond s := by
      have h' := congrArg InfTopHom.complDual h
      simpa [box] using h'
    exact (relation_eq_iff_diamond_eq r s).2 hdiamond

end Relational

end LeanMathlib
