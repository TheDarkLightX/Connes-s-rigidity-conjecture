import Mathlib

namespace LeanMathlib.Rigidity

/-- Three polynomial coordinates truncated below degree `n`. -/
abbrev TernaryTruncatedPolynomialVector (n : ℕ) :=
  Fin 3 → Polynomial.degreeLT (ZMod 3) n

/-- Coefficient-array model of three degree-`< n` ternary polynomials. -/
abbrev TernaryTruncatedCoefficients (n : ℕ) :=
  Fin 3 → Fin n → ZMod 3

/-- Truncated polynomials are exactly their first `n` coefficients. -/
noncomputable def ternaryTruncatedPolynomialVectorEquiv (n : ℕ) :
    TernaryTruncatedPolynomialVector n ≃ₗ[ZMod 3]
      TernaryTruncatedCoefficients n :=
  LinearEquiv.piCongrRight fun _ : Fin 3 =>
    Polynomial.degreeLTEquiv (ZMod 3) n

noncomputable instance ternaryTruncatedPolynomialVectorFintype (n : ℕ) :
    Fintype (TernaryTruncatedPolynomialVector n) :=
  Fintype.ofEquiv (TernaryTruncatedCoefficients n)
    (ternaryTruncatedPolynomialVectorEquiv n).symm.toEquiv

/-- The finite invariant predicted for shift `n` has cardinality `3^(3n)`. -/
theorem card_ternaryTruncatedPolynomialVector (n : ℕ) :
    Fintype.card (TernaryTruncatedPolynomialVector n) = 3 ^ (3 * n) := by
  rw [Fintype.card_congr (ternaryTruncatedPolynomialVectorEquiv n).toEquiv]
  simp [TernaryTruncatedCoefficients, Fintype.card_fun, Nat.mul_comm,
    Nat.pow_mul]

/-- Distinct positive shift parameters yield distinct predicted invariant sizes. -/
theorem card_ternaryTruncatedPolynomialVector_injective :
    Function.Injective
      (fun n : ℕ => Fintype.card (TernaryTruncatedPolynomialVector n)) := by
  intro m n h
  rw [card_ternaryTruncatedPolynomialVector,
    card_ternaryTruncatedPolynomialVector] at h
  have hpow : 3 * m = 3 * n := Nat.pow_right_injective (by omega) h
  omega

end LeanMathlib.Rigidity
