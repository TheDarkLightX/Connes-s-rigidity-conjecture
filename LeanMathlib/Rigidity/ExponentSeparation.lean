import Mathlib

namespace LeanMathlib.Rigidity

/-- Positive exponent-difference shift occurring in the first tensor term. -/
def positiveDifferenceShift (n d : ℤ) : ℤ := n - d

/-- Negative exponent-difference shift occurring in the second tensor term. -/
def negativeDifferenceShift (n d : ℤ) : ℤ := d - n

/--
If every original exponent difference has absolute value strictly below `n`,
then the two shifted supports lie on opposite sides of zero. This is the key
finite-support separation in the all-three-coordinate case of the proposed
rank-three symmetric tensor-cube orbit proof.
-/
theorem shifted_difference_supports_disjoint
    (S : Finset ℤ) (n : ℤ)
    (hbound : ∀ d ∈ S, |d| < n) :
    Disjoint
      (S.image (positiveDifferenceShift n))
      (S.image (negativeDifferenceShift n)) := by
  rw [Finset.disjoint_left]
  intro z hzpos hzneg
  obtain ⟨d, hdS, rfl⟩ := Finset.mem_image.mp hzpos
  obtain ⟨e, heS, heq⟩ := Finset.mem_image.mp hzneg
  have hdabs : |d| < n := hbound d hdS
  have heabs : |e| < n := hbound e heS
  have hdle : d ≤ |d| := le_abs_self d
  have hele : e ≤ |e| := le_abs_self e
  have hpos : 0 < positiveDifferenceShift n d := by
    simp [positiveDifferenceShift]
    linarith
  have hneg : negativeDifferenceShift n e < 0 := by
    simp [negativeDifferenceShift]
    linarith
  rw [← heq] at hneg
  linarith

/-- Each positive shifted difference is strictly positive beyond the support bound. -/
theorem positiveDifferenceShift_pos
    (S : Finset ℤ) (n d : ℤ) (hd : d ∈ S)
    (hbound : ∀ e ∈ S, |e| < n) :
    0 < positiveDifferenceShift n d := by
  have hdabs := hbound d hd
  have hdle : d ≤ |d| := le_abs_self d
  simp [positiveDifferenceShift]
  linarith

/-- Each negative shifted difference is strictly negative beyond the support bound. -/
theorem negativeDifferenceShift_neg
    (S : Finset ℤ) (n d : ℤ) (hd : d ∈ S)
    (hbound : ∀ e ∈ S, |e| < n) :
    negativeDifferenceShift n d < 0 := by
  have hdabs := hbound d hd
  have hdle : d ≤ |d| := le_abs_self d
  simp [negativeDifferenceShift]
  linarith

end LeanMathlib.Rigidity
