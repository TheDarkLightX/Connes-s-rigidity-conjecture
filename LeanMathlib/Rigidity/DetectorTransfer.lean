import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace LeanMathlib.Rigidity

/-- Conditional detector margin after discarding a bad mass `β`. -/
def detectorMargin (δ β : ℚ) : ℚ :=
  (δ - β) / (1 - β)

/--
Abstract detector-transfer inequality.

If total detected mass is at least `δ`, detected bad mass is at most `β`,
and primitive mass is exactly `1-β`, then the detected proportion inside the
primitive part is at least `(δ-β)/(1-β)`.
-/
theorem detector_transfer
    (δ β detectedGood detectedBad primitiveMass : ℚ)
    (hβ : β < 1)
    (hdetected : δ ≤ detectedGood + detectedBad)
    (hbad : detectedBad ≤ β)
    (hprimitive : primitiveMass = 1 - β) :
    detectorMargin δ β ≤ detectedGood / primitiveMass := by
  have hprimpos : 0 < primitiveMass := by
    rw [hprimitive]
    linarith
  rw [detectorMargin, hprimitive]
  apply (div_le_div_iff_of_pos_right (by linarith : 0 < (1 - β))).2
  have hgood : δ - β ≤ detectedGood := by linarith
  simpa using hgood

/-- Binary rank-four parameters recover OpenAI's `1/7` margin. -/
theorem detectorMargin_binary_rank_four :
    detectorMargin (1 / 4) (1 / 8) = 1 / 7 := by
  norm_num [detectorMargin]

/-- Ternary rank-three parameters yield the positive margin `1/8`. -/
theorem detectorMargin_ternary_rank_three :
    detectorMargin (2 / 9) (1 / 9) = 1 / 8 := by
  norm_num [detectorMargin]

/-- The ternary rank-three margin is strictly positive. -/
theorem detectorMargin_ternary_rank_three_pos :
    0 < detectorMargin (2 / 9) (1 / 9) := by
  norm_num [detectorMargin]

/-- The ternary detector support exceeds the nonprimitive density by `1/9`. -/
theorem ternary_detector_absolute_gap :
    (2 / 9 : ℚ) - 1 / 9 = 1 / 9 := by
  norm_num

/-- The two-generator ternary character energy gives the spectral gap `3/8`. -/
theorem ternary_two_generator_detector_energy :
    (3 : ℚ) * detectorMargin (2 / 9) (1 / 9) = 3 / 8 := by
  norm_num [detectorMargin]

/-- Average support contributed by the charts on which a detector is nonzero. -/
def chartMargin (rank degree support : ℚ) : ℚ :=
  (rank - degree) / rank * support

/-- Binary rank-three affine charts recover Zhou's `1/12` detector constant. -/
theorem chartMargin_binary_rank_three :
    chartMargin 3 2 (1 / 4) = 1 / 12 := by
  norm_num [chartMargin]

/-- The strengthened chart count gives `1/8` in binary rank four. -/
theorem chartMargin_binary_rank_four :
    chartMargin 4 2 (1 / 4) = 1 / 8 := by
  norm_num [chartMargin]

/-- The strengthened chart count gives `4/45` in ternary rank five. -/
theorem chartMargin_ternary_rank_five :
    chartMargin 5 3 (2 / 9) = 4 / 45 := by
  norm_num [chartMargin]

end LeanMathlib.Rigidity
