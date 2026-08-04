import Mathlib

namespace LeanMathlib.Rigidity

/--
Reduced polynomial data over `𝔽₃` in `n` variables. At each variable the
exponent is restricted to `0`, `1`, or `2`, so this is also the canonical
coefficient model for all functions `(𝔽₃)^n → 𝔽₃`.
-/
def TernaryReducedPolynomial : ℕ → Type
  | 0 => ZMod 3
  | n + 1 => TernaryReducedPolynomial n ×
      TernaryReducedPolynomial n × TernaryReducedPolynomial n

abbrev TernaryPoly := TernaryReducedPolynomial

private def ternaryPolyAddCommGroup :
    (n : ℕ) → AddCommGroup (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyAddCommGroup n
      infer_instance

attribute [instance] ternaryPolyAddCommGroup

private def ternaryPolyModule :
    (n : ℕ) → Module (ZMod 3) (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyModule n
      infer_instance

attribute [instance] ternaryPolyModule

private def ternaryPolyDecidableEq :
    (n : ℕ) → DecidableEq (TernaryPoly n)
  | 0 => inferInstance
  | n + 1 => by
      letI := ternaryPolyDecidableEq n
      infer_instance

attribute [instance] ternaryPolyDecidableEq

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
  | succ n ih => simp [TernaryReducedPolynomial, ternaryPolyEval, ih]

@[simp]
theorem ternaryPolyEval_add {n : ℕ}
    (p q : TernaryPoly n) (x : Fin n → ZMod 3) :
    ternaryPolyEval (p + q) x =
      ternaryPolyEval p x + ternaryPolyEval q x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [TernaryReducedPolynomial, ternaryPolyEval, ih]
      ring

@[simp]
theorem ternaryPolyEval_smul {n : ℕ}
    (c : ZMod 3) (p : TernaryPoly n) (x : Fin n → ZMod 3) :
    ternaryPolyEval (c • p) x = c * ternaryPolyEval p x := by
  induction n with
  | zero => simp [TernaryReducedPolynomial, ternaryPolyEval]
  | succ n ih =>
      simp [TernaryReducedPolynomial, ternaryPolyEval, ih]
      ring

/-- The slice obtained by fixing the first variable. -/
def ternaryPolySlice {n : ℕ}
    (a : ZMod 3) (p : TernaryPoly (n + 1)) : TernaryPoly n :=
  p.1 + a • p.2.1 + a ^ 2 • p.2.2

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
  have hp₀ : p₀ = (-a) • (p₁ + a • p₂) := by
    change p₀ + a • p₁ + a ^ 2 • p₂ = 0 at hzero
    apply eq_neg_of_add_eq_zero_left
    calc
      a • p₁ + a ^ 2 • p₂ = a • (p₁ + a • p₂) := by
        simp [smul_add, mul_smul, pow_two]
      _ = -((-a) • (p₁ + a • p₂)) := by
        simp
  ext <;> simp [ternaryPolyLinearFactorProduct, hp₀,
    smul_add, mul_smul, pow_two]

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
  have hweighted : (2 : ZMod 3) • p₁ + p₂ = 0 := by
    simpa [ternaryPolySlice, hp₀, pow_two, add_assoc] using h2
  have hp₂ : p₂ = -p₁ := eq_neg_of_add_eq_zero_left hsum
  have hp₁ : p₁ = 0 := by
    rw [hp₂] at hweighted
    simpa [two_smul] using hweighted
  have hp₂zero : p₂ = 0 := by simpa [hp₁] using hp₂
  ext <;> simp [hp₀, hp₁, hp₂zero]

/-- Evaluation on all assignments is injective for reduced ternary polynomials. -/
theorem ternaryPoly_ext_of_eval_eq {n : ℕ}
    (p q : TernaryPoly n)
    (h : ∀ x, ternaryPolyEval p x = ternaryPolyEval q x) :
    p = q := by
  induction n with
  | zero =>
      simpa [TernaryReducedPolynomial, ternaryPolyEval] using h (fun i => Fin.elim0 i)
  | succ n ih =>
      apply Prod.ext
      · apply ih
        intro x
        have hx := h (prependTernary 0 x)
        simpa [ternaryPolyEval_prepend, ternaryPolySlice] using hx
      · apply Prod.ext
        · apply ih
          intro x
          have h0 := h (prependTernary 0 x)
          have h1 := h (prependTernary 1 x)
          have h2 := h (prependTernary 2 x)
          have hslices :
              ternaryPolySlice 0 (p - q) = 0 ∧
              ternaryPolySlice 1 (p - q) = 0 ∧
              ternaryPolySlice 2 (p - q) = 0 := by
            constructor
            · apply ih
              intro y
              simpa [ternaryPolyEval_prepend] using sub_eq_zero.mpr (h (prependTernary 0 y))
            constructor
            · apply ih
              intro y
              simpa [ternaryPolyEval_prepend] using sub_eq_zero.mpr (h (prependTernary 1 y))
            · apply ih
              intro y
              simpa [ternaryPolyEval_prepend] using sub_eq_zero.mpr (h (prependTernary 2 y))
          have hpq : p - q = 0 :=
            ternaryPoly_eq_zero_of_all_slices_zero (p - q)
              hslices.1 hslices.2.1 hslices.2.2
          exact congrArg (fun r : TernaryPoly (n + 1) => r.2.1)
            (sub_eq_zero.mp hpq)
        · have hslices :
              ternaryPolySlice 0 (p - q) = 0 ∧
              ternaryPolySlice 1 (p - q) = 0 ∧
              ternaryPolySlice 2 (p - q) = 0 := by
            constructor
            · apply ih
              intro y
              simpa [ternaryPolyEval_prepend] using sub_eq_zero.mpr (h (prependTernary 0 y))
            constructor
            · apply ih
              intro y
              simpa [ternaryPolyEval_prepend] using sub_eq_zero.mpr (h (prependTernary 1 y))
            · apply ih
              intro y
              simpa [ternaryPolyEval_prepend] using sub_eq_zero.mpr (h (prependTernary 2 y))
          have hpq : p - q = 0 :=
            ternaryPoly_eq_zero_of_all_slices_zero (p - q)
              hslices.1 hslices.2.1 hslices.2.2
          exact congrArg (fun r : TernaryPoly (n + 1) => r.2.2)
            (sub_eq_zero.mp hpq)

end LeanMathlib.Rigidity
