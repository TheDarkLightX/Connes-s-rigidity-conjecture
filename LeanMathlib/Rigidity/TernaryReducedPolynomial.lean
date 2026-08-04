import Mathlib

namespace LeanMathlib.Rigidity

/--
Reduced polynomial data over `𝔽₃` in `n` variables. At each variable the
exponent is restricted to `0`, `1`, or `2`, so this is also the canonical
coefficient model for all functions `(𝔽₃)^n → 𝔽₃`.
-/
@[reducible]
def TernaryReducedPolynomial : ℕ → Type
  | 0 => ZMod 3
  | n + 1 => TernaryReducedPolynomial n ×
      TernaryReducedPolynomial n × TernaryReducedPolynomial n

abbrev TernaryPoly := TernaryReducedPolynomial

@[reducible]
private def ternaryPolyAddCommGroup :
    (n : ℕ) → AddCommGroup (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyAddCommGroup n
      infer_instance

attribute [instance] ternaryPolyAddCommGroup

@[reducible]
private def ternaryPolyModule :
    (n : ℕ) → Module (ZMod 3) (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyModule n
      infer_instance

attribute [instance] ternaryPolyModule

@[reducible]
private def ternaryPolyDecidableEq :
    (n : ℕ) → DecidableEq (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyDecidableEq n
      infer_instance

attribute [instance] ternaryPolyDecidableEq

@[reducible]
private def ternaryPolyFintype :
    (n : ℕ) → Fintype (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyFintype n
      infer_instance

attribute [instance] ternaryPolyFintype

/-- Prepend one ternary coordinate to an assignment. -/
def prependTernary {n : ℕ} (a : ZMod 3) (x : Fin n → ZMod 3) :
    Fin (n + 1) → ZMod 3 :=
  Fin.cases a x

@[simp]
theorem prependTernary_zero {n : ℕ} (a : ZMod 3)
    (x : Fin n → ZMod 3) :
    prependTernary a x 0 = a := rfl

@[simp]
theorem prependTernary_succ {n : ℕ} (a : ZMod 3)
    (x : Fin n → ZMod 3) (i : Fin n) :
    prependTernary a x i.succ = x i := rfl

/-- Evaluate a reduced ternary polynomial. -/
def ternaryPolyEval : {n : ℕ} →
    TernaryPoly n → (Fin n → ZMod 3) → ZMod 3
  | 0, p, _ => p
  | _ + 1, p, x =>
      ternaryPolyEval p.1 (fun i => x i.succ) +
        x 0 * ternaryPolyEval p.2.1 (fun i => x i.succ) +
        (x 0) ^ 2 * ternaryPolyEval p.2.2 (fun i => x i.succ)

@[simp]
theorem ternaryPolyEval_zero {n : ℕ} (x : Fin n → ZMod 3) :
    ternaryPolyEval (0 : TernaryPoly n) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ternaryPolyEval, ih]

@[simp]
theorem ternaryPolyEval_add {n : ℕ}
    (p q : TernaryPoly n) (x : Fin n → ZMod 3) :
    ternaryPolyEval (p + q) x =
      ternaryPolyEval p x + ternaryPolyEval q x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [ternaryPolyEval, ih]
      ring

@[simp]
theorem ternaryPolyEval_smul {n : ℕ}
    (c : ZMod 3) (p : TernaryPoly n) (x : Fin n → ZMod 3) :
    ternaryPolyEval (c • p) x = c * ternaryPolyEval p x := by
  induction n with
  | zero => simp [ternaryPolyEval]
  | succ n ih =>
      simp [ternaryPolyEval, ih]
      ring

@[simp]
theorem ternaryPolyEval_neg {n : ℕ}
    (p : TernaryPoly n) (x : Fin n → ZMod 3) :
    ternaryPolyEval (-p) x = -ternaryPolyEval p x := by
  have h := ternaryPolyEval_smul (-1 : ZMod 3) p x
  simpa using h

@[simp]
theorem ternaryPolyEval_sub {n : ℕ}
    (p q : TernaryPoly n) (x : Fin n → ZMod 3) :
    ternaryPolyEval (p - q) x =
      ternaryPolyEval p x - ternaryPolyEval q x := by
  simp [sub_eq_add_neg]

/-- The slice obtained by fixing the first variable. -/
def ternaryPolySlice {n : ℕ}
    (a : ZMod 3) (p : TernaryPoly (n + 1)) : TernaryPoly n :=
  p.1 + a • p.2.1 + a ^ 2 • p.2.2

@[simp]
theorem ternaryPolySlice_sub {n : ℕ}
    (a : ZMod 3) (p q : TernaryPoly (n + 1)) :
    ternaryPolySlice a (p - q) =
      ternaryPolySlice a p - ternaryPolySlice a q := by
  change (p.1 - q.1) + a • (p.2.1 - q.2.1) +
      a ^ 2 • (p.2.2 - q.2.2) =
    (p.1 + a • p.2.1 + a ^ 2 • p.2.2) -
      (q.1 + a • q.2.1 + a ^ 2 • q.2.2)
  module

@[simp]
theorem ternaryPolyEval_prepend {n : ℕ}
    (a : ZMod 3) (p : TernaryPoly (n + 1))
    (x : Fin n → ZMod 3) :
    ternaryPolyEval p (prependTernary a x) =
      ternaryPolyEval (ternaryPolySlice a p) x := by
  simp [ternaryPolyEval, ternaryPolySlice]
  ring

/-- Quotient coefficients after a zero slice at `a`. -/
def ternaryPolyFactorQuotient {n : ℕ}
    (a : ZMod 3) (p : TernaryPoly (n + 1)) : TernaryPoly (n + 1) :=
  (p.2.1 + a • p.2.2, p.2.2, 0)

/-- Rebuild `(t-a)q` when `q` has first-variable degree at most one. -/
def ternaryPolyLinearFactorProduct {n : ℕ}
    (a : ZMod 3) (q₀ q₁ : TernaryPoly n) : TernaryPoly (n + 1) :=
  ((-a) • q₀, q₀ - a • q₁, q₁)

/-- A vanishing slice gives an exact linear factorization in coefficient data. -/
theorem ternaryPoly_factorization_of_slice_zero {n : ℕ}
    (a : ZMod 3) (p : TernaryPoly (n + 1))
    (hzero : ternaryPolySlice a p = 0) :
    p = ternaryPolyLinearFactorProduct a
      (p.2.1 + a • p.2.2) p.2.2 := by
  rcases p with ⟨p₀, p₁, p₂⟩
  change (p₀, p₁, p₂) = _
  have hsum : p₀ + (a • p₁ + a ^ 2 • p₂) = 0 := by
    simpa [ternaryPolySlice, add_assoc] using hzero
  have hp₀ : p₀ = (-a) • (p₁ + a • p₂) := by
    have hp₀neg : p₀ = -(a • p₁ + a ^ 2 • p₂) :=
      eq_neg_of_add_eq_zero_left hsum
    calc
      p₀ = -(a • p₁ + a ^ 2 • p₂) := hp₀neg
      _ = (-a) • (p₁ + a • p₂) := by module
  simp [ternaryPolyLinearFactorProduct, hp₀]

/-- Evaluation form of exact division by a vanishing linear slice. -/
theorem ternaryPoly_eval_factorization {n : ℕ}
    (a : ZMod 3) (p : TernaryPoly (n + 1))
    (hzero : ternaryPolySlice a p = 0)
    (x : Fin (n + 1) → ZMod 3) :
    ternaryPolyEval p x =
      (x 0 - a) *
        ternaryPolyEval (ternaryPolyFactorQuotient a p) x := by
  rw [ternaryPoly_factorization_of_slice_zero a p hzero]
  simp [ternaryPolyLinearFactorProduct,
    ternaryPolyFactorQuotient, ternaryPolyEval]
  ring

/-- If a reduced polynomial vanishes on all three slices, all coefficients vanish. -/
theorem ternaryPoly_eq_zero_of_all_slices_zero {n : ℕ}
    (p : TernaryPoly (n + 1))
    (h0 : ternaryPolySlice 0 p = 0)
    (h1 : ternaryPolySlice 1 p = 0)
    (h2 : ternaryPolySlice 2 p = 0) :
    p = 0 := by
  rcases p with ⟨p₀, p₁, p₂⟩
  have hp₀ : p₀ = 0 := by
    simpa [ternaryPolySlice] using h0
  have hsum : p₁ + p₂ = 0 := by
    simpa [ternaryPolySlice, hp₀, add_assoc] using h1
  have hsquare : (2 : ZMod 3) ^ 2 = 1 := by native_decide
  have h2' :
      p₀ + (2 : ZMod 3) • p₁ + (2 : ZMod 3) ^ 2 • p₂ = 0 := by
    simpa [ternaryPolySlice] using h2
  have hweighted : (2 : ZMod 3) • p₁ + p₂ = 0 := by
    rw [hp₀, hsquare, zero_add, one_smul] at h2'
    exact h2'
  have hp₁neg : p₁ = -p₂ := eq_neg_of_add_eq_zero_left hsum
  have hp₂ : p₂ = -p₁ := by
    calc
      p₂ = -(-p₂) := by simp
      _ = -p₁ := by rw [hp₁neg]
  have hp₁ : p₁ = 0 := by
    rw [hp₂] at hweighted
    simpa [two_smul] using hweighted
  have hp₂zero : p₂ = 0 := by simpa [hp₁] using hp₂
  change (p₀, p₁, p₂) = ((0 : TernaryPoly n), 0, 0)
  exact Prod.ext hp₀ (Prod.ext hp₁ hp₂zero)

/-- Evaluation on all assignments is injective for reduced ternary polynomials. -/
theorem ternaryPoly_ext_of_eval_eq {n : ℕ}
    (p q : TernaryPoly n)
    (h : ∀ x, ternaryPolyEval p x = ternaryPolyEval q x) :
    p = q := by
  induction n with
  | zero =>
      simpa [ternaryPolyEval] using h (fun i => Fin.elim0 i)
  | succ n ih =>
      have hslice (a : ZMod 3) :
          ternaryPolySlice a p = ternaryPolySlice a q := by
        apply ih
        intro y
        simpa only [ternaryPolyEval_prepend] using h (prependTernary a y)
      have hz0 : ternaryPolySlice 0 (p - q) = 0 := by
        rw [ternaryPolySlice_sub, hslice 0, sub_self]
      have hz1 : ternaryPolySlice 1 (p - q) = 0 := by
        rw [ternaryPolySlice_sub, hslice 1, sub_self]
      have hz2 : ternaryPolySlice 2 (p - q) = 0 := by
        rw [ternaryPolySlice_sub, hslice 2, sub_self]
      exact sub_eq_zero.mp
        (ternaryPoly_eq_zero_of_all_slices_zero (p - q) hz0 hz1 hz2)

end LeanMathlib.Rigidity
