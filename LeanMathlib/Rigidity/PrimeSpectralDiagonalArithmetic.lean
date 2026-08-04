import Mathlib

namespace LeanMathlib.Rigidity

/--
Every interior binomial coefficient in row `p` vanishes in characteristic `p`.
This is the prime-uniform arithmetic core of the spectral diagonal lemma.
-/
theorem prime_choose_cast_eq_zero
    {p j : ℕ} (hp : p.Prime) (hj0 : j ≠ 0) (hjp : j < p) :
    ((p.choose j : ℕ) : ZMod p) = 0 := by
  rw [CharP.cast_eq_zero_iff (ZMod p) p]
  exact hp.dvd_choose_self hj0 hjp

/-- Multiplying by an interior row-`p` binomial coefficient is zero over `F_p`. -/
theorem prime_choose_mul_eq_zero
    {p j : ℕ} (hp : p.Prime) (hj0 : j ≠ 0) (hjp : j < p)
    (x : ZMod p) :
    ((p.choose j : ℕ) : ZMod p) * x = 0 := by
  rw [prime_choose_cast_eq_zero hp hj0 hjp, zero_mul]

/-- The ternary `e_1` and `e_2` multiplicities are both zero in `F_3`. -/
example (x : ZMod 3) :
    ((Nat.choose 3 1 : ℕ) : ZMod 3) * x = 0 ∧
      ((Nat.choose 3 2 : ℕ) : ZMod 3) * x = 0 := by
  constructor
  · exact prime_choose_mul_eq_zero (by norm_num) (by norm_num) (by norm_num) x
  · exact prime_choose_mul_eq_zero (by norm_num) (by norm_num) (by norm_num) x

end LeanMathlib.Rigidity
