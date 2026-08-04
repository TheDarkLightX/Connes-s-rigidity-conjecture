import Mathlib
import LeanMathlib.Rigidity.TernarySupportRecurrence

namespace LeanMathlib.Rigidity

/-- Minimum support for degree zero in `n` ternary variables. -/
def ternaryWeightZero (n : ℕ) : ℕ := 3 ^ n

/-- Minimum support for degree at most one. -/
def ternaryWeightOne : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * 3 ^ n

/-- Minimum support for degree at most two. -/
def ternaryWeightTwo : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 ^ n

/-- Minimum support for degree at most three. -/
def ternaryWeightThree : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * 3 ^ n

/-- Degree-one recurrence from the zero-slice trichotomy. -/
theorem ternaryWeightOne_succ (n : ℕ) :
    ternaryWeightOne (n + 1) =
      min (3 * ternaryWeightOne n)
        (min (2 * ternaryWeightZero n) (2 * ternaryWeightZero n)) := by
  cases n with
  | zero => norm_num [ternaryWeightOne, ternaryWeightZero]
  | succ n =>
      simp [ternaryWeightOne, ternaryWeightZero, pow_succ]
      omega

/-- Degree-two recurrence from zero, one, or two vanishing slices. -/
theorem ternaryWeightTwo_succ (n : ℕ) :
    ternaryWeightTwo (n + 1) =
      min (3 * ternaryWeightTwo n)
        (min (2 * ternaryWeightOne n) (ternaryWeightZero n)) := by
  cases n with
  | zero => norm_num [ternaryWeightTwo, ternaryWeightOne, ternaryWeightZero]
  | succ n =>
      simp [ternaryWeightTwo, ternaryWeightOne,
        ternaryWeightZero, pow_succ]
      omega

/-- Degree-three recurrence from zero, one, or two vanishing slices. -/
theorem ternaryWeightThree_succ (n : ℕ) :
    ternaryWeightThree (n + 1) =
      min (3 * ternaryWeightThree n)
        (min (2 * ternaryWeightTwo n) (ternaryWeightOne n)) := by
  cases n with
  | zero => norm_num [ternaryWeightThree, ternaryWeightTwo, ternaryWeightOne]
  | succ n =>
      cases n with
      | zero => norm_num [ternaryWeightThree, ternaryWeightTwo, ternaryWeightOne]
      | succ n =>
          simp [ternaryWeightThree, ternaryWeightTwo,
            ternaryWeightOne, pow_succ]
          omega

/-- A nonzero surviving slice remains nonzero after division by another zero slice. -/
theorem ternaryPolyFactorQuotient_slice_ne_zero {n : ℕ}
    (a b : ZMod 3) (hab : b ≠ a)
    (p : TernaryPoly (n + 1))
    (ha : ternaryPolySlice a p = 0)
    (hb : ternaryPolySlice b p ≠ 0) :
    ternaryPolySlice b (ternaryPolyFactorQuotient a p) ≠ 0 := by
  intro hq
  apply hb
  apply ternaryPoly_ext_of_eval_eq _ 0
  intro x
  rw [ternaryPoly_slice_factor_eval a b p ha, hq]
  simp

/-- Simultaneous minimum-support theorem for degrees zero through three. -/
theorem ternaryMinimumSupportAll :
    ∀ n : ℕ,
      (∀ (p : TernaryPoly n), TernaryDegreeZero p → p ≠ 0 →
        ternaryWeightZero n ≤ ternaryPolySupportCard p) ∧
      (∀ (p : TernaryPoly n), TernaryDegreeOne p → p ≠ 0 →
        ternaryWeightOne n ≤ ternaryPolySupportCard p) ∧
      (∀ (p : TernaryPoly n), TernaryDegreeTwo p → p ≠ 0 →
        ternaryWeightTwo n ≤ ternaryPolySupportCard p) ∧
      (∀ (p : TernaryPoly n), TernaryDegreeThree p → p ≠ 0 →
        ternaryWeightThree n ≤ ternaryPolySupportCard p)
  | 0 => by
      constructor
      · intro p hdeg hp
        have hpos := ternaryPolySupportCard_pos hp
        simpa [ternaryWeightZero] using hpos
      constructor
      · intro p hdeg hp
        have hpos := ternaryPolySupportCard_pos hp
        simpa [ternaryWeightOne] using hpos
      constructor
      · intro p hdeg hp
        have hpos := ternaryPolySupportCard_pos hp
        simpa [ternaryWeightTwo] using hpos
      · intro p hdeg hp
        have hpos := ternaryPolySupportCard_pos hp
        simpa [ternaryWeightThree] using hpos
  | n + 1 => by
      have ih := ternaryMinimumSupportAll n
      let ih₀ := ih.1
      let ih₁ := ih.2.1
      let ih₂ := ih.2.2.1
      let ih₃ := ih.2.2.2
      constructor
      · intro p hdeg hp
        rw [ternaryWeightZero]
        exact (ternaryDegreeZero_supportCard p hdeg hp).ge
      constructor
      · intro p hdeg hp
        rw [ternaryWeightOne_succ]
        apply ternaryPolySupportCard_lower_of_slice_bounds p hp
        · intro a ha
          exact ih₁ _ (ternaryPolyDegreeLE_slice a hdeg) ha
        · intro a b hab ha hb
          let q := ternaryPolyFactorQuotient a p
          have hqdeg : TernaryDegreeZero q :=
            ternaryPolyFactorQuotient_degreeZero a hdeg
          have hqb : ternaryPolySlice b q ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero a b (Ne.symm hab) p ha hb
          have hbound := ih₀ _ (ternaryPolyDegreeLE_slice b hqdeg) hqb
          rw [ternaryPolySupportCard_factorSlice a b (Ne.symm hab) p ha]
          exact hbound
        · intro a b c hab hca hcb ha hb hc
          let q := ternaryPolyFactorQuotient a p
          have hqdeg : TernaryDegreeZero q :=
            ternaryPolyFactorQuotient_degreeZero a hdeg
          have hqbzero : ternaryPolySlice b q = 0 :=
            ternaryPolyFactorQuotient_slice_zero a b (Ne.symm hab) p ha hb
          have hqne : q ≠ 0 :=
            ternaryPolyFactorQuotient_ne_zero a hp ha
          exact (hqne (ternaryDegreeZero_eq_zero_of_slice_zero
            q hqdeg b hqbzero)).elim
      constructor
      · intro p hdeg hp
        rw [ternaryWeightTwo_succ]
        apply ternaryPolySupportCard_lower_of_slice_bounds p hp
        · intro a ha
          exact ih₂ _ (ternaryPolyDegreeLE_slice a hdeg) ha
        · intro a b hab ha hb
          let q := ternaryPolyFactorQuotient a p
          have hqdeg : TernaryDegreeOne q :=
            ternaryPolyFactorQuotient_degreeOne a hdeg
          have hqb : ternaryPolySlice b q ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero a b (Ne.symm hab) p ha hb
          have hbound := ih₁ _ (ternaryPolyDegreeLE_slice b hqdeg) hqb
          rw [ternaryPolySupportCard_factorSlice a b (Ne.symm hab) p ha]
          exact hbound
        · intro a b c hab hca hcb ha hb hc
          let q := ternaryPolyFactorQuotient a p
          have hqdeg : TernaryDegreeOne q :=
            ternaryPolyFactorQuotient_degreeOne a hdeg
          have hqbzero : ternaryPolySlice b q = 0 :=
            ternaryPolyFactorQuotient_slice_zero a b (Ne.symm hab) p ha hb
          let r := ternaryPolyFactorQuotient b q
          have hrdeg : TernaryDegreeZero r :=
            ternaryPolyFactorQuotient_degreeZero b hqdeg
          have hqc : ternaryPolySlice c q ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero a c hca p ha hc
          have hrc : ternaryPolySlice c r ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero b c hcb q hqbzero hqc
          have hbound := ih₀ _ (ternaryPolyDegreeLE_slice c hrdeg) hrc
          rw [ternaryPolySupportCard_factorSlice a c hca p ha,
            ternaryPolySupportCard_factorSlice b c hcb q hqbzero]
          exact hbound
      · intro p hdeg hp
        rw [ternaryWeightThree_succ]
        apply ternaryPolySupportCard_lower_of_slice_bounds p hp
        · intro a ha
          exact ih₃ _ (ternaryPolyDegreeLE_slice a hdeg) ha
        · intro a b hab ha hb
          let q := ternaryPolyFactorQuotient a p
          have hqdeg : TernaryDegreeTwo q :=
            ternaryPolyFactorQuotient_degreeTwo a hdeg
          have hqb : ternaryPolySlice b q ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero a b (Ne.symm hab) p ha hb
          have hbound := ih₂ _ (ternaryPolyDegreeLE_slice b hqdeg) hqb
          rw [ternaryPolySupportCard_factorSlice a b (Ne.symm hab) p ha]
          exact hbound
        · intro a b c hab hca hcb ha hb hc
          let q := ternaryPolyFactorQuotient a p
          have hqdeg : TernaryDegreeTwo q :=
            ternaryPolyFactorQuotient_degreeTwo a hdeg
          have hqbzero : ternaryPolySlice b q = 0 :=
            ternaryPolyFactorQuotient_slice_zero a b (Ne.symm hab) p ha hb
          let r := ternaryPolyFactorQuotient b q
          have hrdeg : TernaryDegreeOne r :=
            ternaryPolyFactorQuotient_degreeOne b hqdeg
          have hqc : ternaryPolySlice c q ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero a c hca p ha hc
          have hrc : ternaryPolySlice c r ≠ 0 :=
            ternaryPolyFactorQuotient_slice_ne_zero b c hcb q hqbzero hqc
          have hbound := ih₁ _ (ternaryPolyDegreeLE_slice c hrdeg) hrc
          rw [ternaryPolySupportCard_factorSlice a c hca p ha,
            ternaryPolySupportCard_factorSlice b c hcb q hqbzero]
          exact hbound

/-- Nonzero degree-at-most-one ternary polynomials have the Reed--Muller bound. -/
theorem ternaryDegreeOne_minimumSupport {n : ℕ}
    (p : TernaryPoly n) (hdeg : TernaryDegreeOne p) (hp : p ≠ 0) :
    ternaryWeightOne n ≤ ternaryPolySupportCard p :=
  (ternaryMinimumSupportAll n).2.1 p hdeg hp

/-- Nonzero degree-at-most-two ternary polynomials have the Reed--Muller bound. -/
theorem ternaryDegreeTwo_minimumSupport {n : ℕ}
    (p : TernaryPoly n) (hdeg : TernaryDegreeTwo p) (hp : p ≠ 0) :
    ternaryWeightTwo n ≤ ternaryPolySupportCard p :=
  (ternaryMinimumSupportAll n).2.2.1 p hdeg hp

/--
Specialized generalized Reed--Muller minimum-distance theorem needed by the
rank-three ternary carry construction: a nonzero reduced polynomial of total
degree at most three in `n+2` variables is nonzero on at least `2*3^n` points.
-/
theorem ternaryDegreeThree_minimumSupport
    (n : ℕ) (p : TernaryPoly (n + 2))
    (hdeg : TernaryDegreeThree p) (hp : p ≠ 0) :
    2 * 3 ^ n ≤ ternaryPolySupportCard p := by
  simpa [ternaryWeightThree] using
    (ternaryMinimumSupportAll (n + 2)).2.2.2 p hdeg hp

/-- Equivalent integer form of the `2/9` relative support bound. -/
theorem ternaryDegreeThree_two_ninths
    (n : ℕ) (p : TernaryPoly (n + 2))
    (hdeg : TernaryDegreeThree p) (hp : p ≠ 0) :
    2 * 3 ^ (n + 2) ≤ 9 * ternaryPolySupportCard p := by
  have h := ternaryDegreeThree_minimumSupport n p hdeg hp
  rw [show 3 ^ (n + 2) = 9 * 3 ^ n by ring]
  omega

end LeanMathlib.Rigidity
