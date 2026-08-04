import Mathlib

namespace LeanMathlib.Rigidity

/--
Coefficient-level group-like equation for a finitely supported vector on an
arbitrary basis type. This is the diagonal coproduct equation of a group
algebra, expressed without assuming that the underlying group is finite.
-/
def FinsuppGroupLikeEquation {G K : Type*} [DecidableEq G] [Zero K] [Mul K]
    (a : G →₀ K) : Prop :=
  ∀ g h, (if g = h then a g else 0) = a g * a h

/--
Arbitrary-group version of exact group reconstruction from a Hopf coproduct.
A finitely supported coefficient vector with counit one and diagonal coproduct
equal to its tensor square is exactly one basis vector with coefficient one.
-/
theorem exact_groupLike_finsupp
    {G K : Type*} [DecidableEq G] [Field K]
    (a : G →₀ K)
    (hcounit : a.sum (fun _ c => c) = 1)
    (hcomul : FinsuppGroupLikeEquation a) :
    ∃ g, a = Finsupp.single g 1 := by
  have ha_ne_zero : a ≠ 0 := by
    intro ha
    subst a
    simp at hcounit
  have hnonzero : ∃ g, a g ≠ 0 := by
    by_contra h
    push_neg at h
    apply ha_ne_zero
    ext g
    simp [h g]
  obtain ⟨g, hg⟩ := hnonzero
  have hdiag := hcomul g g
  simp [FinsuppGroupLikeEquation] at hdiag
  have hgone : a g = 1 := by
    have hcancel : (1 : K) * a g = a g * a g := by simpa using hdiag
    have hone : (1 : K) = a g := mul_right_cancel₀ hg hcancel
    exact hone.symm
  refine ⟨g, ?_⟩
  ext h
  by_cases hh : h = g
  · subst h
    simp [hgone]
  · have hgh : g ≠ h := by
      intro hEq
      exact hh hEq.symm
    have hoff := hcomul g h
    simp [FinsuppGroupLikeEquation, hgh, hgone] at hoff
    simp [Finsupp.single_apply, hgh, hoff]

/-- Every basis vector with coefficient one satisfies the exact group-like equations. -/
theorem single_satisfies_groupLike_finsupp
    {G K : Type*} [DecidableEq G] [Field K]
    (g : G) :
    (Finsupp.single g (1 : K)).sum (fun _ c => c) = 1 ∧
      FinsuppGroupLikeEquation (Finsupp.single g 1) := by
  constructor
  · simp
  · intro x y
    by_cases hxy : x = y <;>
      by_cases hx : x = g <;>
      by_cases hy : y = g <;>
      simp [FinsuppGroupLikeEquation, Finsupp.single_apply, hxy, hx, hy]

/-- Exact characterization of group-like finitely supported coefficient vectors. -/
theorem groupLike_finsupp_iff_single
    {G K : Type*} [DecidableEq G] [Field K]
    (a : G →₀ K) :
    (a.sum (fun _ c => c) = 1 ∧ FinsuppGroupLikeEquation a) ↔
      ∃ g, a = Finsupp.single g 1 := by
  constructor
  · rintro ⟨hcounit, hcomul⟩
    exact exact_groupLike_finsupp a hcounit hcomul
  · rintro ⟨g, rfl⟩
    exact single_satisfies_groupLike_finsupp (K := K) g

end LeanMathlib.Rigidity
