import LeanMathlib.Order.StoneSeparation
import Mathlib.Topology.Compactification.StoneCech

namespace LeanMathlib

open Filter

namespace Stone

variable {α : Type*}

/-- The basic clopen set determined by a subset of the underlying type. -/
def basicClopen (s : Set α) : Set (Ultrafilter α) :=
  { u | s ∈ u }

@[simp] theorem mem_basicClopen_iff {u : Ultrafilter α} {s : Set α} :
    u ∈ basicClopen s ↔ s ∈ u := by
  rfl

theorem isOpen_basicClopen (s : Set α) : IsOpen (basicClopen s) := by
  simpa [basicClopen] using ultrafilter_isOpen_basic (α := α) s

theorem isClosed_basicClopen (s : Set α) : IsClosed (basicClopen s) := by
  simpa [basicClopen] using ultrafilter_isClosed_basic (α := α) s

theorem isClopen_basicClopen (s : Set α) : IsClopen (basicClopen s) :=
  ⟨isClosed_basicClopen s, isOpen_basicClopen s⟩

@[simp] theorem principalPoint_mem_basicClopen_iff {a : α} {s : Set α} :
    principalPoint a ∈ basicClopen s ↔ a ∈ s := by
  simp [basicClopen, principalPoint]

theorem basicClopen_injective : Function.Injective (basicClopen : Set α → Set (Ultrafilter α)) := by
  intro s t hst
  apply (set_eq_iff_forall_principalPoint_mem (s := s) (t := t)).2
  intro a
  simpa [basicClopen] using congrArg (fun z => principalPoint a ∈ z) hst

theorem basicClopen_eq_iff {s t : Set α} :
    basicClopen s = basicClopen t ↔ s = t := by
  constructor
  · intro h
    exact basicClopen_injective h
  · intro h
    simp [h]

theorem basicClopen_ne_iff_exists_principalPoint_distinguishing {s t : Set α} :
    basicClopen s ≠ basicClopen t ↔
      ∃ a : α, ((principalPoint a ∈ basicClopen s ∧ principalPoint a ∉ basicClopen t) ∨
        (principalPoint a ∈ basicClopen t ∧ principalPoint a ∉ basicClopen s)) := by
  constructor
  · intro h
    have hst : s ≠ t := by
      intro hEq
      exact h (by simp [hEq])
    rcases (set_ne_iff_exists_principalPoint_distinguishing (s := s) (t := t)).1 hst with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [basicClopen] using ha
  · rintro ⟨a, (⟨hs, htn⟩ | ⟨ht, hsn⟩)⟩ hEq
    · exact htn (hEq ▸ hs)
    · exact hsn (hEq ▸ ht)

end Stone

end LeanMathlib
