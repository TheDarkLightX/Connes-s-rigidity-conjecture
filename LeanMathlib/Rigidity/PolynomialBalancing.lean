import Mathlib

namespace LeanMathlib.Rigidity

/--
In a domain, a nonzero coefficient cannot be balanced between two distinct
polynomial-coordinate actions. This is the algebraic cancellation step behind
the proposed rank-three transvection argument: an equality of the form
`t₁ A = t₂ A` forces `A = 0` because `t₁ - t₂` is not a zero divisor.
-/
theorem balancing_forces_zero
    {R : Type*} [CommRing R] [IsDomain R]
    {x y a : R} (hxy : x ≠ y) (hbalance : x * a = y * a) :
    a = 0 := by
  have hzero : (x - y) * a = 0 := by
    rw [sub_mul, hbalance, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hxy)

/-- Contrapositive form used to certify that a transvection moves a nonzero tensor block. -/
theorem distinct_coordinate_actions_move
    {R : Type*} [CommRing R] [IsDomain R]
    {x y a : R} (hxy : x ≠ y) (ha : a ≠ 0) :
    x * a ≠ y * a := by
  intro hbalance
  exact ha (balancing_forces_zero hxy hbalance)

/-- The binary detector constant from the rank-four construction is `1/7`. -/
theorem binary_rank_four_detector_margin :
    ((((1 : ℚ) / 4) - 1 / 8) / (1 - 1 / 8)) = 1 / 7 := by
  norm_num

/-- The proposed ternary rank-three detector constant is `1/8`. -/
theorem ternary_rank_three_detector_margin :
    ((((2 : ℚ) / 9) - 1 / 9) / (1 - 1 / 9)) = 1 / 8 := by
  norm_num

/-- The ternary rank-three detector has a strict positive margin. -/
theorem ternary_rank_three_detector_margin_pos :
    (0 : ℚ) < (((2 / 9) - 1 / 9) / (1 - 1 / 9)) := by
  norm_num

end LeanMathlib.Rigidity
