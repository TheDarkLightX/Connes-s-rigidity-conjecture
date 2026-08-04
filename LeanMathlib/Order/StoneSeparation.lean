import LeanMathlib.Order.AtomicBooleanAlgebra
import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.Filter.Ultrafilter.Defs

namespace LeanMathlib

open Filter
open scoped symmDiff

namespace Stone

variable {α : Type*}

/-- The principal ultrafilter at a point. -/
def principalPoint (a : α) : Ultrafilter α :=
  pure a

@[simp] theorem mem_principalPoint_iff {a : α} {s : Set α} :
    s ∈ principalPoint a ↔ a ∈ s := by
  simp [principalPoint]

theorem principalPoint_ext {a b : α}
    (h : principalPoint a = principalPoint b) :
    a = b := by
  exact Ultrafilter.pure_injective <| by simpa [principalPoint] using h

theorem principalPoint_injective : Function.Injective (principalPoint : α → Ultrafilter α) := by
  intro a b h
  exact principalPoint_ext h

theorem principalPoint_eq_iff {a b : α} :
    principalPoint a = principalPoint b ↔ a = b := by
  constructor
  · exact principalPoint_ext
  · intro h
    simp [h]

theorem exists_principalPoint_mem_symmDiff_of_set_ne {s t : Set α}
    (hst : s ≠ t) :
    ∃ a : α, ({a} : Set α) ≤ s ∆ t := by
  rcases Set.symmDiff_nonempty.2 hst with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro x hx
  have hx' : x = a := by simpa using hx
  subst x
  exact ha

theorem exists_principal_ultrafilter_distinguishing_of_set_ne {s t : Set α}
    (hst : s ≠ t) :
    ∃ a : α, ((s ∈ principalPoint a ∧ t ∉ principalPoint a) ∨
      (t ∈ principalPoint a ∧ s ∉ principalPoint a)) := by
  rcases Set.symmDiff_nonempty.2 hst with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [Set.mem_symmDiff] at ha
  rcases ha with (⟨hs, htn⟩ | ⟨ht, hsn⟩)
  · exact Or.inl ⟨by simpa [principalPoint] using hs, by simpa [principalPoint] using htn⟩
  · exact Or.inr ⟨by simpa [principalPoint] using ht, by simpa [principalPoint] using hsn⟩

theorem exists_ultrafilter_distinguishing_of_set_ne {s t : Set α}
    (hst : s ≠ t) :
    ∃ u : Ultrafilter α, (s ∈ u ∧ t ∉ u) ∨ (t ∈ u ∧ s ∉ u) := by
  rcases exists_principal_ultrafilter_distinguishing_of_set_ne (s := s) (t := t) hst with
    ⟨a, ha⟩
  exact ⟨principalPoint a, ha⟩

theorem set_eq_iff_forall_principalPoint_mem {s t : Set α} :
    s = t ↔ ∀ a : α, (s ∈ principalPoint a ↔ t ∈ principalPoint a) := by
  constructor
  · intro h a
    simp [h]
  · intro h
    ext a
    simpa [principalPoint] using h a

theorem set_ne_iff_exists_principalPoint_distinguishing {s t : Set α} :
    s ≠ t ↔
      ∃ a : α, ((s ∈ principalPoint a ∧ t ∉ principalPoint a) ∨
        (t ∈ principalPoint a ∧ s ∉ principalPoint a)) := by
  constructor
  · exact exists_principal_ultrafilter_distinguishing_of_set_ne
  · rintro ⟨a, (⟨hs, htn⟩ | ⟨ht, hsn⟩)⟩ hEq
    · exact htn (hEq ▸ hs)
    · exact hsn (hEq ▸ ht)

end Stone

end LeanMathlib
