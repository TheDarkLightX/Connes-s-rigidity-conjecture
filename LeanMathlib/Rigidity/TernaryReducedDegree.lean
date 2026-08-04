import Mathlib
import LeanMathlib.Rigidity.TernaryReducedPolynomial

namespace LeanMathlib.Rigidity

/-- Total-degree-at-most predicate for recursive reduced ternary polynomials. -/
def ternaryPolyDegreeLE : (d n : ℕ) → TernaryPoly n → Prop
  | _, 0, _ => True
  | 0, n + 1, p =>
      ternaryPolyDegreeLE 0 n p.1 ∧ p.2.1 = 0 ∧ p.2.2 = 0
  | 1, n + 1, p =>
      ternaryPolyDegreeLE 1 n p.1 ∧
        ternaryPolyDegreeLE 0 n p.2.1 ∧ p.2.2 = 0
  | d + 2, n + 1, p =>
      ternaryPolyDegreeLE (d + 2) n p.1 ∧
        ternaryPolyDegreeLE (d + 1) n p.2.1 ∧
        ternaryPolyDegreeLE d n p.2.2

abbrev TernaryDegreeZero {n : ℕ} := ternaryPolyDegreeLE 0 n
abbrev TernaryDegreeOne {n : ℕ} := ternaryPolyDegreeLE 1 n
abbrev TernaryDegreeTwo {n : ℕ} := ternaryPolyDegreeLE 2 n
abbrev TernaryDegreeThree {n : ℕ} := ternaryPolyDegreeLE 3 n

@[simp]
theorem ternaryPolyDegreeLE_zero (d n : ℕ) :
    ternaryPolyDegreeLE d n (0 : TernaryPoly n) := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases d with
      | zero => simp [ternaryPolyDegreeLE, ih]
      | succ d =>
          cases d with
          | zero => simp [ternaryPolyDegreeLE, ih]
          | succ d => simp [ternaryPolyDegreeLE, ih]

/-- Degree bounds are closed under addition. -/
theorem ternaryPolyDegreeLE_add {d n : ℕ}
    {p q : TernaryPoly n}
    (hp : ternaryPolyDegreeLE d n p)
    (hq : ternaryPolyDegreeLE d n q) :
    ternaryPolyDegreeLE d n (p + q) := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases d with
      | zero =>
          rcases hp with ⟨hp₀, hp₁, hp₂⟩
          rcases hq with ⟨hq₀, hq₁, hq₂⟩
          refine ⟨ih hp₀ hq₀, ?_, ?_⟩
          · change p.2.1 + q.2.1 = 0
            rw [hp₁, hq₁, zero_add]
          · change p.2.2 + q.2.2 = 0
            rw [hp₂, hq₂, zero_add]
      | succ d =>
          cases d with
          | zero =>
              rcases hp with ⟨hp₀, hp₁, hp₂⟩
              rcases hq with ⟨hq₀, hq₁, hq₂⟩
              refine ⟨ih hp₀ hq₀, ih hp₁ hq₁, ?_⟩
              change p.2.2 + q.2.2 = 0
              rw [hp₂, hq₂, zero_add]
          | succ d =>
              rcases hp with ⟨hp₀, hp₁, hp₂⟩
              rcases hq with ⟨hq₀, hq₁, hq₂⟩
              exact ⟨ih hp₀ hq₀, ih hp₁ hq₁, ih hp₂ hq₂⟩

/-- Degree bounds are closed under scalar multiplication. -/
theorem ternaryPolyDegreeLE_smul {d n : ℕ}
    (c : ZMod 3) {p : TernaryPoly n}
    (hp : ternaryPolyDegreeLE d n p) :
    ternaryPolyDegreeLE d n (c • p) := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases d with
      | zero =>
          rcases hp with ⟨hp₀, hp₁, hp₂⟩
          refine ⟨ih hp₀, ?_, ?_⟩
          · change c • p.2.1 = 0
            rw [hp₁, smul_zero]
          · change c • p.2.2 = 0
            rw [hp₂, smul_zero]
      | succ d =>
          cases d with
          | zero =>
              rcases hp with ⟨hp₀, hp₁, hp₂⟩
              refine ⟨ih hp₀, ih hp₁, ?_⟩
              change c • p.2.2 = 0
              rw [hp₂, smul_zero]
          | succ d =>
              rcases hp with ⟨hp₀, hp₁, hp₂⟩
              exact ⟨ih hp₀, ih hp₁, ih hp₂⟩

/-- Raising the allowed degree preserves the predicate. -/
theorem ternaryPolyDegreeLE_succ {d n : ℕ}
    {p : TernaryPoly n}
    (hp : ternaryPolyDegreeLE d n p) :
    ternaryPolyDegreeLE (d + 1) n p := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases d with
      | zero =>
          rcases hp with ⟨hp₀, hp₁, hp₂⟩
          exact ⟨ih hp₀, by simpa [hp₁] using
            (ternaryPolyDegreeLE_zero 0 n), hp₂⟩
      | succ d =>
          cases d with
          | zero =>
              rcases hp with ⟨hp₀, hp₁, hp₂⟩
              exact ⟨ih hp₀, ih hp₁, by simpa [hp₂] using
                (ternaryPolyDegreeLE_zero 0 n)⟩
          | succ d =>
              rcases hp with ⟨hp₀, hp₁, hp₂⟩
              exact ⟨ih hp₀, ih hp₁, ih hp₂⟩

/-- Arbitrary monotonicity in the degree allowance. -/
theorem ternaryPolyDegreeLE_mono {d e n : ℕ}
    (hde : d ≤ e) {p : TernaryPoly n}
    (hp : ternaryPolyDegreeLE d n p) :
    ternaryPolyDegreeLE e n p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  clear hde
  induction k with
  | zero => simpa
  | succ k ih =>
      simpa [Nat.add_assoc] using ternaryPolyDegreeLE_succ ih

/-- Fixing one variable does not increase total degree. -/
theorem ternaryPolyDegreeLE_slice {d n : ℕ}
    (a : ZMod 3) {p : TernaryPoly (n + 1)}
    (hp : ternaryPolyDegreeLE d (n + 1) p) :
    ternaryPolyDegreeLE d n (ternaryPolySlice a p) := by
  cases d with
  | zero =>
      rcases hp with ⟨hp₀, hp₁, hp₂⟩
      simpa [ternaryPolySlice, hp₁, hp₂] using hp₀
  | succ d =>
      cases d with
      | zero =>
          rcases hp with ⟨hp₀, hp₁, hp₂⟩
          apply ternaryPolyDegreeLE_add
          · exact ternaryPolyDegreeLE_add hp₀
              (ternaryPolyDegreeLE_smul a
                (ternaryPolyDegreeLE_succ hp₁))
          · simpa [hp₂] using ternaryPolyDegreeLE_zero 1 n
      | succ d =>
          rcases hp with ⟨hp₀, hp₁, hp₂⟩
          apply ternaryPolyDegreeLE_add
          · exact ternaryPolyDegreeLE_add hp₀
              (ternaryPolyDegreeLE_smul a
                (ternaryPolyDegreeLE_succ hp₁))
          · exact ternaryPolyDegreeLE_smul (a ^ 2)
              (ternaryPolyDegreeLE_mono (by omega) hp₂)

/-- One zero slice lowers a degree-one polynomial to degree zero. -/
theorem ternaryPolyFactorQuotient_degreeZero {n : ℕ}
    (a : ZMod 3) {p : TernaryPoly (n + 1)}
    (hp : TernaryDegreeOne p) :
    TernaryDegreeZero (ternaryPolyFactorQuotient a p) := by
  rcases hp with ⟨hp₀, hp₁, hp₂⟩
  change ternaryPolyDegreeLE 0 n (p.2.1 + a • p.2.2) ∧
    p.2.2 = 0 ∧ (0 : TernaryPoly n) = 0
  refine ⟨?_, hp₂, rfl⟩
  simpa [hp₂] using hp₁

/-- One zero slice lowers a degree-two polynomial to degree one. -/
theorem ternaryPolyFactorQuotient_degreeOne {n : ℕ}
    (a : ZMod 3) {p : TernaryPoly (n + 1)}
    (hp : TernaryDegreeTwo p) :
    TernaryDegreeOne (ternaryPolyFactorQuotient a p) := by
  rcases hp with ⟨hp₀, hp₁, hp₂⟩
  refine ⟨?_, hp₂, rfl⟩
  exact ternaryPolyDegreeLE_add hp₁
    (ternaryPolyDegreeLE_smul a (ternaryPolyDegreeLE_succ hp₂))

/-- One zero slice lowers a degree-three polynomial to degree two. -/
theorem ternaryPolyFactorQuotient_degreeTwo {n : ℕ}
    (a : ZMod 3) {p : TernaryPoly (n + 1)}
    (hp : TernaryDegreeThree p) :
    TernaryDegreeTwo (ternaryPolyFactorQuotient a p) := by
  rcases hp with ⟨hp₀, hp₁, hp₂⟩
  refine ⟨?_, hp₂, ternaryPolyDegreeLE_zero 0 n⟩
  exact ternaryPolyDegreeLE_add hp₁
    (ternaryPolyDegreeLE_smul a (ternaryPolyDegreeLE_succ hp₂))

/-- The factor quotient is nonzero whenever the original polynomial is. -/
theorem ternaryPolyFactorQuotient_ne_zero {n : ℕ}
    (a : ZMod 3) {p : TernaryPoly (n + 1)}
    (hp : p ≠ 0) (hzero : ternaryPolySlice a p = 0) :
    ternaryPolyFactorQuotient a p ≠ 0 := by
  intro hq
  apply hp
  apply ternaryPoly_ext_of_eval_eq p 0
  intro x
  rw [ternaryPoly_eval_factorization a p hzero x]
  simp [hq]

/-- Slice evaluation after factoring a zero slice. -/
theorem ternaryPoly_slice_factor_eval {n : ℕ}
    (a b : ZMod 3) (p : TernaryPoly (n + 1))
    (hzero : ternaryPolySlice a p = 0)
    (x : Fin n → ZMod 3) :
    ternaryPolyEval (ternaryPolySlice b p) x =
      (b - a) * ternaryPolyEval
        (ternaryPolySlice b (ternaryPolyFactorQuotient a p)) x := by
  rw [← ternaryPolyEval_prepend,
    ternaryPoly_eval_factorization a p hzero,
    ternaryPolyEval_prepend]
  rfl

/-- A second zero slice descends to the factor quotient. -/
theorem ternaryPolyFactorQuotient_slice_zero {n : ℕ}
    (a b : ZMod 3) (hab : b ≠ a)
    (p : TernaryPoly (n + 1))
    (ha : ternaryPolySlice a p = 0)
    (hb : ternaryPolySlice b p = 0) :
    ternaryPolySlice b (ternaryPolyFactorQuotient a p) = 0 := by
  apply ternaryPoly_ext_of_eval_eq _ 0
  intro x
  have hfactor := ternaryPoly_slice_factor_eval a b p ha x
  rw [hb, ternaryPolyEval_zero] at hfactor
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  have hz := (mul_eq_zero.mp hfactor.symm).resolve_left hba
  simpa using hz

end LeanMathlib.Rigidity
