import LeanMathlib.Order.StoneBasicClopen

namespace LeanMathlib

open Filter

namespace Stone

variable {α β γ : Type*}

@[simp] theorem mem_map_basicClopen_iff {m : α → β} {u : Ultrafilter α} {s : Set β} :
    Ultrafilter.map m u ∈ basicClopen s ↔ u ∈ basicClopen (m ⁻¹' s) := by
  simp [basicClopen, Ultrafilter.mem_map]

theorem preimage_basicClopen_map (m : α → β) (s : Set β) :
    (Ultrafilter.map m) ⁻¹' basicClopen s = basicClopen (m ⁻¹' s) := by
  ext u
  simp [basicClopen, Ultrafilter.mem_map]

@[simp] theorem map_principalPoint (m : α → β) (a : α) :
    Ultrafilter.map m (principalPoint a) = principalPoint (m a) := by
  rw [principalPoint, principalPoint, Ultrafilter.map_pure]

@[simp] theorem map_principalPoint_mem_basicClopen_iff {m : α → β} {a : α} {s : Set β} :
    Ultrafilter.map m (principalPoint a) ∈ basicClopen s ↔ m a ∈ s := by
  simp [map_principalPoint]

@[simp] theorem principalPoint_mem_preimage_basicClopen_map_iff {m : α → β} {a : α} {s : Set β} :
    principalPoint a ∈ (Ultrafilter.map m) ⁻¹' basicClopen s ↔ m a ∈ s := by
  simp [preimage_basicClopen_map]

theorem preimage_basicClopen_map_comp (f : α → β) (g : β → γ) (s : Set γ) :
    (Ultrafilter.map (g ∘ f)) ⁻¹' basicClopen s =
      (Ultrafilter.map f) ⁻¹' ((Ultrafilter.map g) ⁻¹' basicClopen s) := by
  ext u
  change (((g ∘ f) ⁻¹' s) ∈ u ↔ (f ⁻¹' (g ⁻¹' s)) ∈ u)
  rfl

theorem preimage_basicClopen_eq_iff (m : α → β) {s t : Set β} :
    (Ultrafilter.map m) ⁻¹' basicClopen s = (Ultrafilter.map m) ⁻¹' basicClopen t ↔
      m ⁻¹' s = m ⁻¹' t := by
  rw [preimage_basicClopen_map, preimage_basicClopen_map, basicClopen_eq_iff]

theorem preimage_basicClopen_eq_iff_of_surjective {m : α → β} (hm : Function.Surjective m)
    {s t : Set β} :
    (Ultrafilter.map m) ⁻¹' basicClopen s = (Ultrafilter.map m) ⁻¹' basicClopen t ↔ s = t := by
  rw [preimage_basicClopen_eq_iff]
  constructor
  · intro hpre
    ext b
    rcases hm b with ⟨a, rfl⟩
    simpa using congrArg (fun z => a ∈ z) hpre
  · intro h
    simp [h]

end Stone

end LeanMathlib
