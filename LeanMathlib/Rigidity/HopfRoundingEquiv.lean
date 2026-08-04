import Mathlib
import LeanMathlib.Rigidity.HopfRounding

namespace LeanMathlib.Rigidity

/-- Two-sided metric rounding gives a left inverse below half the basis separation. -/
theorem metric_rounding_leftInverse
    {G H U : Type*}
    [Group G] [Group H] [Group U] [PseudoMetricSpace U]
    (F : G →* U) (basis : H →* U)
    (round : G → H) (back : H → G)
    (δ separation : ℝ)
    (hround : ∀ g, dist (F g) (basis (round g)) ≤ δ)
    (hback : ∀ h, dist (basis h) (F (back h)) ≤ δ)
    (hseparatedF : ∀ g g', g ≠ g' →
      separation ≤ dist (F g) (F g'))
    (hgap : 2 * δ < separation) :
    Function.LeftInverse back round := by
  intro g
  by_contra hne
  have hlower : separation ≤ dist (F (back (round g))) (F g) :=
    hseparatedF _ _ hne
  have hupper : dist (F (back (round g))) (F g) ≤ 2 * δ := by
    calc
      dist (F (back (round g))) (F g) ≤
          dist (F (back (round g))) (basis (round g)) +
            dist (basis (round g)) (F g) := dist_triangle _ _ _
      _ ≤ δ + δ := by
        exact add_le_add
          (by simpa [dist_comm] using hback (round g))
          (by simpa [dist_comm] using hround g)
      _ = 2 * δ := by ring
  linarith

/-- Two-sided metric rounding gives a right inverse below half the basis separation. -/
theorem metric_rounding_rightInverse
    {G H U : Type*}
    [Group G] [Group H] [Group U] [PseudoMetricSpace U]
    (F : G →* U) (basis : H →* U)
    (round : G → H) (back : H → G)
    (δ separation : ℝ)
    (hround : ∀ g, dist (F g) (basis (round g)) ≤ δ)
    (hback : ∀ h, dist (basis h) (F (back h)) ≤ δ)
    (hseparatedBasis : ∀ h h', h ≠ h' →
      separation ≤ dist (basis h) (basis h'))
    (hgap : 2 * δ < separation) :
    Function.RightInverse back round := by
  intro h
  by_contra hne
  have hlower : separation ≤
      dist (basis (round (back h))) (basis h) :=
    hseparatedBasis _ _ hne
  have hupper : dist (basis (round (back h))) (basis h) ≤ 2 * δ := by
    calc
      dist (basis (round (back h))) (basis h) ≤
          dist (basis (round (back h))) (F (back h)) +
            dist (F (back h)) (basis h) := dist_triangle _ _ _
      _ ≤ δ + δ := by
        exact add_le_add
          (by simpa [dist_comm] using hround (back h))
          (by simpa [dist_comm] using hback h)
      _ = 2 * δ := by ring
  linarith

/-- A multiplicative rounding map between groups automatically preserves one. -/
theorem map_one_of_map_mul
    {G H : Type*} [Group G] [Group H]
    (f : G → H) (hmul : ∀ g h, f (g * h) = f g * f h) :
    f 1 = 1 := by
  have h := hmul 1 1
  simp only [one_mul] at h
  have h' := congrArg (fun x => (f 1)⁻¹ * x) h
  simpa [mul_assoc] using h'

/-- Package multiplicative rounding as a group homomorphism. -/
def roundingGroupHom
    {G H : Type*} [Group G] [Group H]
    (round : G → H)
    (hmul : ∀ g h, round (g * h) = round g * round h) : G →* H where
  toFun := round
  map_one' := map_one_of_map_mul round hmul
  map_mul' := hmul

/--
Quantitative reconstruction theorem.

If two exact group representations in a metric group round to each other
within `δ`, multiplication is 1-Lipschitz, and distinct basis points are
separated by `separation`, then `3δ < separation` forces a group isomorphism.
-/
noncomputable def groupMulEquivOfMetricRounding
    {G H U : Type*}
    [Group G] [Group H] [Group U] [PseudoMetricSpace U]
    (F : G →* U) (basis : H →* U)
    (round : G → H) (back : H → G)
    (δ separation : ℝ)
    (hmul : ∀ a b c d : U,
      dist (a * b) (c * d) ≤ dist a c + dist b d)
    (hround : ∀ g, dist (F g) (basis (round g)) ≤ δ)
    (hback : ∀ h, dist (basis h) (F (back h)) ≤ δ)
    (hseparatedF : ∀ g g', g ≠ g' →
      separation ≤ dist (F g) (F g'))
    (hseparatedBasis : ∀ h h', h ≠ h' →
      separation ≤ dist (basis h) (basis h'))
    (hgap : 3 * δ < separation) : G ≃* H := by
  have hgap2 : 2 * δ < separation := by
    have hδnonneg : 0 ≤ δ := by
      have := dist_nonneg
      by_contra hneg
      have hδneg : δ < 0 := lt_of_not_ge hneg
      specialize hround 1
      have : dist (F 1) (basis (round 1)) < 0 := lt_of_le_of_lt hround hδneg
      exact (not_lt_of_ge dist_nonneg) this
    linarith
  have hmulRound := rounding_multiplicative F basis round δ separation
    hmul hround hseparatedBasis hgap
  let hom := roundingGroupHom round hmulRound
  have hleft := metric_rounding_leftInverse F basis round back δ separation
    hround hback hseparatedF hgap2
  have hright := metric_rounding_rightInverse F basis round back δ separation
    hround hback hseparatedBasis hgap2
  exact MulEquiv.ofBijective hom
    ⟨hleft.injective, hright.surjective⟩

/-- At group-unitary separation `√2`, defect below `√2/3` forces reconstruction. -/
theorem sqrt_two_thirds_threshold :
    ∀ δ : ℝ, δ < Real.sqrt 2 / 3 → 3 * δ < Real.sqrt 2 := by
  intro δ hδ
  have hthree : (0 : ℝ) < 3 := by norm_num
  nlinarith

end LeanMathlib.Rigidity
