import Mathlib

namespace LeanMathlib.Rigidity

/--
A general metric rounding lemma underlying quantitative Hopf reconstruction.

`F` is an exact multiplicative representation of `G` in a metric group `U`,
`basis` embeds a candidate target group `H`, and `round` assigns to each
`F g` a nearby basis point. If multiplication in `U` is 1-Lipschitz in both
variables and distinct basis points are separated by more than three rounding
errors, then rounding preserves multiplication exactly.
-/
theorem rounding_multiplicative
    {G H U : Type*}
    [Group G] [Group H] [Group U] [PseudoMetricSpace U]
    (F : G →* U) (basis : H →* U) (round : G → H)
    (δ separation : ℝ)
    (hmul : ∀ a b c d : U,
      dist (a * b) (c * d) ≤ dist a c + dist b d)
    (hround : ∀ g, dist (F g) (basis (round g)) ≤ δ)
    (hseparated : ∀ x y : H, x ≠ y → separation ≤ dist (basis x) (basis y))
    (hgap : 3 * δ < separation) :
    ∀ g h, round (g * h) = round g * round h := by
  intro g h
  by_contra hne
  have hlower : separation ≤
      dist (basis (round (g * h))) (basis (round g * round h)) :=
    hseparated _ _ hne
  have hfirst : dist (basis (round (g * h))) (F (g * h)) ≤ δ := by
    simpa [dist_comm] using hround (g * h)
  have hsecond : dist (F (g * h)) (basis (round g * round h)) ≤ 2 * δ := by
    rw [map_mul, map_mul]
    calc
      dist (F g * F h) (basis (round g) * basis (round h)) ≤
          dist (F g) (basis (round g)) + dist (F h) (basis (round h)) :=
        hmul _ _ _ _
      _ ≤ δ + δ := add_le_add (hround g) (hround h)
      _ = 2 * δ := by ring
  have hupper :
      dist (basis (round (g * h))) (basis (round g * round h)) ≤ 3 * δ := by
    calc
      dist (basis (round (g * h))) (basis (round g * round h)) ≤
          dist (basis (round (g * h))) (F (g * h)) +
            dist (F (g * h)) (basis (round g * round h)) :=
        dist_triangle _ _ _
      _ ≤ δ + 2 * δ := add_le_add hfirst hsecond
      _ = 3 * δ := by ring
  linarith

/-- Package a multiplicative rounding function as a monoid homomorphism. -/
def roundingMonoidHom
    {G H U : Type*}
    [Group G] [Group H] [Group U] [PseudoMetricSpace U]
    (F : G →* U) (basis : H →* U) (round : G → H)
    (δ separation : ℝ)
    (hmul : ∀ a b c d : U,
      dist (a * b) (c * d) ≤ dist a c + dist b d)
    (hround : ∀ g, dist (F g) (basis (round g)) ≤ δ)
    (hseparated : ∀ x y : H, x ≠ y → separation ≤ dist (basis x) (basis y))
    (hgap : 3 * δ < separation)
    (hround_one : round 1 = 1) : G →* H where
  toFun := round
  map_one' := hround_one
  map_mul' := rounding_multiplicative F basis round δ separation
    hmul hround hseparated hgap

end LeanMathlib.Rigidity
