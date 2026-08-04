import Mathlib
import LeanMathlib.Rigidity.TernarySupportCore

namespace LeanMathlib.Rigidity

/--
Generic three-slice support recurrence.

* `A` bounds each nonzero slice when no factor is used;
* `B` bounds surviving slices after one zero linear factor;
* `C` bounds the final slice after two zero linear factors.

The result is the minimum of the three possible totals `3A`, `2B`, and `C`.
-/
theorem ternaryPolySupportCard_lower_of_slice_bounds {n : ℕ}
    (p : TernaryPoly (n + 1)) (hp : p ≠ 0)
    (A B C : ℕ)
    (hSame : ∀ a : ZMod 3,
      ternaryPolySlice a p ≠ 0 →
        A ≤ ternaryPolySupportCard (ternaryPolySlice a p))
    (hOne : ∀ a b : ZMod 3, a ≠ b →
      ternaryPolySlice a p = 0 →
      ternaryPolySlice b p ≠ 0 →
        B ≤ ternaryPolySupportCard (ternaryPolySlice b p))
    (hTwo : ∀ a b c : ZMod 3,
      a ≠ b → c ≠ a → c ≠ b →
      ternaryPolySlice a p = 0 →
      ternaryPolySlice b p = 0 →
      ternaryPolySlice c p ≠ 0 →
        C ≤ ternaryPolySupportCard (ternaryPolySlice c p)) :
    min (3 * A) (min (2 * B) C) ≤ ternaryPolySupportCard p := by
  rw [ternaryPolySupportCard_three_slices]
  by_cases h0 : ternaryPolySlice 0 p = 0
  · by_cases h1 : ternaryPolySlice 1 p = 0
    · by_cases h2 : ternaryPolySlice 2 p = 0
      · exact (hp (ternaryPoly_eq_zero_of_all_slices_zero p h0 h1 h2)).elim
      · have hc := hTwo 0 1 2 (by native_decide) (by native_decide)
          (by native_decide) h0 h1 h2
        have hmin : min (3 * A) (min (2 * B) C) ≤ C :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        simp [h0, h1]
        omega
    · by_cases h2 : ternaryPolySlice 2 p = 0
      · have hc := hTwo 0 2 1 (by native_decide) (by native_decide)
          (by native_decide) h0 h2 h1
        have hmin : min (3 * A) (min (2 * B) C) ≤ C :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        simp [h0, h2]
        omega
      · have h1b := hOne 0 1 (by native_decide) h0 h1
        have h2b := hOne 0 2 (by native_decide) h0 h2
        have hmin : min (3 * A) (min (2 * B) C) ≤ 2 * B :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
        simp [h0]
        omega
  · by_cases h1 : ternaryPolySlice 1 p = 0
    · by_cases h2 : ternaryPolySlice 2 p = 0
      · have hc := hTwo 1 2 0 (by native_decide) (by native_decide)
          (by native_decide) h1 h2 h0
        have hmin : min (3 * A) (min (2 * B) C) ≤ C :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        simp [h1, h2]
        omega
      · have h0b := hOne 1 0 (by native_decide) h1 h0
        have h2b := hOne 1 2 (by native_decide) h1 h2
        have hmin : min (3 * A) (min (2 * B) C) ≤ 2 * B :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
        simp [h1]
        omega
    · by_cases h2 : ternaryPolySlice 2 p = 0
      · have h0b := hOne 2 0 (by native_decide) h2 h0
        have h1b := hOne 2 1 (by native_decide) h2 h1
        have hmin : min (3 * A) (min (2 * B) C) ≤ 2 * B :=
          le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
        simp [h2]
        omega
      · have h0b := hSame 0 h0
        have h1b := hSame 1 h1
        have h2b := hSame 2 h2
        have hmin : min (3 * A) (min (2 * B) C) ≤ 3 * A :=
          Nat.min_le_left _ _
        omega

/-- A degree-zero reduced polynomial is determined by every slice. -/
theorem ternaryDegreeZero_slice_eq_base {n : ℕ}
    (p : TernaryPoly (n + 1))
    (hp : TernaryDegreeZero p)
    (a : ZMod 3) :
    ternaryPolySlice a p = p.1 := by
  rcases hp with ⟨hp₀, hp₁, hp₂⟩
  simp [ternaryPolySlice, hp₁, hp₂]

/-- A degree-zero polynomial with one zero slice is the zero polynomial. -/
theorem ternaryDegreeZero_eq_zero_of_slice_zero {n : ℕ}
    (p : TernaryPoly (n + 1))
    (hp : TernaryDegreeZero p)
    (a : ZMod 3)
    (hzero : ternaryPolySlice a p = 0) :
    p = 0 := by
  rcases p with ⟨p₀, p₁, p₂⟩
  rcases hp with ⟨hp₀, hp₁, hp₂⟩
  have hp₀zero : p₀ = 0 := by
    simpa [ternaryPolySlice, hp₁, hp₂] using hzero
  ext <;> simp [hp₀zero, hp₁, hp₂]

/-- Exact support size of a nonzero degree-zero reduced ternary polynomial. -/
theorem ternaryDegreeZero_supportCard :
    ∀ {n : ℕ} (p : TernaryPoly n),
      TernaryDegreeZero p → p ≠ 0 →
        ternaryPolySupportCard p = 3 ^ n
  | 0, p, _, hp => by
      fin_cases p <;> native_decide
  | n + 1, p, hdeg, hp => by
      rcases p with ⟨p₀, p₁, p₂⟩
      rcases hdeg with ⟨hp₀deg, hp₁, hp₂⟩
      have hp₀ne : p₀ ≠ 0 := by
        intro hzero
        apply hp
        ext <;> simp [hzero, hp₁, hp₂]
      rw [ternaryPolySupportCard_three_slices]
      simp [ternaryPolySlice, hp₁, hp₂,
        ternaryDegreeZero_supportCard p₀ hp₀deg hp₀ne,
        pow_succ]
      ring

end LeanMathlib.Rigidity
