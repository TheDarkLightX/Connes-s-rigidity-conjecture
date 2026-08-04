import Mathlib

namespace LeanMathlib.Rigidity

/-- Coefficients of a polynomial symmetric in three spectral variables. -/
structure TernarySymmetricCoefficients where
  coeff : ℕ → ℕ → ℕ → ZMod 3
  swap_first_second : ∀ a b c, coeff a b c = coeff b a c
  swap_second_third : ∀ a b c, coeff a b c = coeff a c b

namespace TernarySymmetricCoefficients

/-- Three equal coefficients sum to zero over `F_3`. -/
theorem three_equal_sum_zero (x : ZMod 3) : x + x + x = 0 := by
  calc
    x + x + x = (3 : ZMod 3) * x := by ring
    _ = 0 := by norm_num

/--
The diagonal coefficient in `e_1 f` vanishes for every symmetric ternary
spectral coefficient family. The three possible one-coordinate decrements are
permutations of one another and therefore occur with total coefficient three.
-/
theorem elementaryOne_diagonal_cancellation
    (a : TernarySymmetricCoefficients) (n : ℕ) :
    a.coeff (n - 1) n n +
      a.coeff n (n - 1) n +
      a.coeff n n (n - 1) = 0 := by
  have hsecond :
      a.coeff n (n - 1) n = a.coeff (n - 1) n n := by
    exact (a.swap_first_second (n - 1) n n).symm
  have hthird :
      a.coeff n n (n - 1) = a.coeff (n - 1) n n := by
    calc
      a.coeff n n (n - 1) = a.coeff n (n - 1) n :=
        a.swap_second_third n n (n - 1)
      _ = a.coeff (n - 1) n n := hsecond
  rw [hsecond, hthird]
  exact three_equal_sum_zero _

/--
The diagonal coefficient in `e_2 f` also vanishes. The three possible
complements of a single coordinate are again permutations of one another.
-/
theorem elementaryTwo_diagonal_cancellation
    (a : TernarySymmetricCoefficients) (n : ℕ) :
    a.coeff (n - 1) (n - 1) n +
      a.coeff (n - 1) n (n - 1) +
      a.coeff n (n - 1) (n - 1) = 0 := by
  have hmiddle :
      a.coeff (n - 1) n (n - 1) =
        a.coeff (n - 1) (n - 1) n := by
    exact a.swap_second_third (n - 1) n (n - 1)
  have hlast :
      a.coeff n (n - 1) (n - 1) =
        a.coeff (n - 1) (n - 1) n := by
    exact (a.swap_first_second (n - 1) n (n - 1)).symm
  rw [hmiddle, hlast]
  exact three_equal_sum_zero _

/-- Multiplication by `e_3` shifts all three spectral exponents together. -/
theorem elementaryThree_diagonal_shift
    (a : TernarySymmetricCoefficients) (n : ℕ) :
    a.coeff n n n = a.coeff n n n := rfl

end TernarySymmetricCoefficients

end LeanMathlib.Rigidity
