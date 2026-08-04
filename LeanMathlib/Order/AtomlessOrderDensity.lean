import LeanMathlib.Order.AtomlessBooleanAlgebra

namespace LeanMathlib

section Atomless

variable {α : Type*} [BooleanAlgebra α] [IsAtomless α]

/--
Atomless Boolean algebras have a dense order: between any strict inclusion
there is another element.
-/
theorem exists_between_of_lt {a b : α} (hab : a < b) :
    ∃ c : α, a < c ∧ c < b := by
  let r : α := rightSplit b a
  have hr0 : r ≠ ⊥ := exists_nonzero_rightSplit hab
  obtain ⟨d, hd0, hdr⟩ := exists_lt_nonzero hr0
  refine ⟨a ⊔ d, ?_, ?_⟩
  · have hdr_le : d ≤ r := hdr.le
    have hd_le_compl : d ≤ aᶜ := by
      exact le_trans hdr_le (by simp [r, rightSplit_eq_inf_compl])
    have hnot : ¬ d ≤ a := by
      intro hda
      have hbot_le : d ≤ (⊥ : α) := by
        have hmeet : d ≤ a ⊓ aᶜ := le_inf hda hd_le_compl
        simpa using hmeet
      exact hd0 (le_bot_iff.mp hbot_le)
    refine lt_of_le_of_ne le_sup_left ?_
    intro hac
    exact hnot (le_trans (le_sup_right : d ≤ a ⊔ d) (le_of_eq hac.symm))
  · have hdr_le : d ≤ r := hdr.le
    have hd_le_b : d ≤ b := le_trans hdr_le (rightSplit_le_left b a)
    have hle : a ⊔ d ≤ b := sup_le hab.le hd_le_b
    refine lt_of_le_of_ne hle ?_
    intro hcb
    have hr_le_d : r ≤ d := by
      have hr_le_sup : r ≤ a ⊔ d := by
        simpa [hcb] using (rightSplit_le_left b a : r ≤ b)
      have hr_le_compl : r ≤ aᶜ := by
        simp [r, rightSplit_eq_inf_compl]
      calc
        r = r ⊓ (a ⊔ d) := by
          exact (inf_eq_left.mpr hr_le_sup).symm
        _ = r ⊓ d := by
          calc
            r ⊓ (a ⊔ d) = (r ⊓ a) ⊔ (r ⊓ d) := by
              rw [inf_sup_left]
            _ = ⊥ ⊔ (r ⊓ d) := by
              have hra_bot : r ⊓ a = (⊥ : α) := by
                have hle_bot : r ⊓ a ≤ (⊥ : α) := by
                  have hle_inf : r ⊓ a ≤ aᶜ ⊓ a := inf_le_inf hr_le_compl le_rfl
                  simpa [inf_comm, inf_left_comm, inf_assoc] using hle_inf
                exact le_bot_iff.mp hle_bot
              rw [hra_bot]
            _ = r ⊓ d := by simp
        _ ≤ d := inf_le_right
    exact hdr.ne (le_antisymm hdr.le hr_le_d)

end Atomless

end LeanMathlib
