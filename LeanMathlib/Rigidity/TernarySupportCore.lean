import Mathlib
import LeanMathlib.Rigidity.TernaryReducedDegree

namespace LeanMathlib.Rigidity

/-- Assignments where a reduced ternary polynomial evaluates nontrivially. -/
abbrev TernaryPolySupport {n : ℕ} (p : TernaryPoly n) :=
  {x : Fin n → ZMod 3 // ternaryPolyEval p x ≠ 0}

/-- Number of nonzero evaluations. -/
def ternaryPolySupportCard {n : ℕ} (p : TernaryPoly n) : ℕ :=
  Fintype.card (TernaryPolySupport p)

/-- Split an assignment into its first coordinate and tail. -/
def ternaryAssignmentEquiv (n : ℕ) :
    (Fin (n + 1) → ZMod 3) ≃
      ZMod 3 × (Fin n → ZMod 3) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := prependTernary x.1 x.2
  left_inv := by
    intro x
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv := by
    intro x
    apply Prod.ext
    · rfl
    · funext i
      rfl

/-- Support in `n+1` variables is the disjoint union of the three slice supports. -/
noncomputable def ternaryPolySupportSliceEquiv {n : ℕ}
    (p : TernaryPoly (n + 1)) :
    TernaryPolySupport p ≃
      Σ a : ZMod 3, TernaryPolySupport (ternaryPolySlice a p) where
  toFun x := by
    let a := x.val 0
    let y : Fin n → ZMod 3 := fun i => x.val i.succ
    refine ⟨a, ⟨y, ?_⟩⟩
    have hxrepr : prependTernary a y = x.val := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
    have hx := x.property
    rw [← hxrepr, ternaryPolyEval_prepend] at hx
    exact hx
  invFun x :=
    ⟨prependTernary x.1 x.2.val,
      by simpa [ternaryPolyEval_prepend] using x.2.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv := by
    rintro ⟨a, ⟨y, hy⟩⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl

/-- Exact support-card recursion through the three slices. -/
theorem ternaryPolySupportCard_slices {n : ℕ}
    (p : TernaryPoly (n + 1)) :
    ternaryPolySupportCard p =
      ∑ a : ZMod 3, ternaryPolySupportCard (ternaryPolySlice a p) := by
  unfold ternaryPolySupportCard
  rw [Fintype.card_congr (ternaryPolySupportSliceEquiv p)]
  exact Fintype.card_sigma

/-- Explicit three-slice cardinal formula. -/
theorem ternaryPolySupportCard_three_slices {n : ℕ}
    (p : TernaryPoly (n + 1)) :
    ternaryPolySupportCard p =
      ternaryPolySupportCard (ternaryPolySlice 0 p) +
      ternaryPolySupportCard (ternaryPolySlice 1 p) +
      ternaryPolySupportCard (ternaryPolySlice 2 p) := by
  classical
  rw [ternaryPolySupportCard_slices]
  decide

@[simp]
theorem ternaryPolySupportCard_zero (n : ℕ) :
    ternaryPolySupportCard (0 : TernaryPoly n) = 0 := by
  classical
  simp [ternaryPolySupportCard, TernaryPolySupport]

/-- Support equivalence for a nonzero slice after dividing by a zero linear factor. -/
noncomputable def ternaryPolyFactorSliceSupportEquiv {n : ℕ}
    (a b : ZMod 3) (hab : b ≠ a)
    (p : TernaryPoly (n + 1))
    (ha : ternaryPolySlice a p = 0) :
    TernaryPolySupport (ternaryPolySlice b p) ≃
      TernaryPolySupport
        (ternaryPolySlice b (ternaryPolyFactorQuotient a p)) where
  toFun x := by
    refine ⟨x.val, ?_⟩
    intro hzero
    apply x.property
    rw [ternaryPoly_slice_factor_eval a b p ha, hzero, mul_zero]
  invFun x := by
    refine ⟨x.val, ?_⟩
    rw [ternaryPoly_slice_factor_eval a b p ha]
    exact mul_ne_zero (sub_ne_zero.mpr hab) x.property
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Factoring a zero slice preserves support size on every other slice. -/
theorem ternaryPolySupportCard_factorSlice {n : ℕ}
    (a b : ZMod 3) (hab : b ≠ a)
    (p : TernaryPoly (n + 1))
    (ha : ternaryPolySlice a p = 0) :
    ternaryPolySupportCard (ternaryPolySlice b p) =
      ternaryPolySupportCard
        (ternaryPolySlice b (ternaryPolyFactorQuotient a p)) := by
  exact Fintype.card_congr
    (ternaryPolyFactorSliceSupportEquiv a b hab p ha)

/-- A nonzero reduced polynomial has positive support. -/
theorem ternaryPolySupportCard_pos {n : ℕ}
    {p : TernaryPoly n} (hp : p ≠ 0) :
    0 < ternaryPolySupportCard p := by
  have hex : ∃ x : Fin n → ZMod 3, ternaryPolyEval p x ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply ternaryPoly_ext_of_eval_eq p 0
    intro x
    simpa using h x
  obtain ⟨x, hx⟩ := hex
  exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩

end LeanMathlib.Rigidity
