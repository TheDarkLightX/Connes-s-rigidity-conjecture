import Mathlib
import LeanMathlib.Rigidity.DividedCubeSymmetry
import LeanMathlib.Rigidity.TernaryWittCarry

namespace LeanMathlib.Rigidity

/-- Predicate selecting equal exponent triples. -/
def IsDiagonalTriple (e : TripleExponent) : Prop :=
  e.first = e.second ∧ e.second = e.third

/-- Diagonal exponent triples. -/
abbrev DiagonalTriple := {e : TripleExponent // IsDiagonalTriple e}

/-- A diagonal exponent triple is uniquely determined by its common exponent. -/
def diagonalTripleEquivNat : DiagonalTriple ≃ ℕ where
  toFun e := e.1.first
  invFun n := ⟨⟨n, n, n⟩, rfl, rfl⟩
  left_inv := by
    intro e
    apply Subtype.ext
    rcases e with ⟨⟨a, b, c⟩, hab, hbc⟩
    simp [IsDiagonalTriple] at hab hbc ⊢
    omega
  right_inv := by intro n; rfl

/-- Restrict a triple coefficient block to equal exponents. -/
noncomputable def diagonalBlockFinsupp
    {R : Type*} [Semiring R] (A : TripleBlock R) : ℕ →₀ R :=
  (Finsupp.domCongr diagonalTripleEquivNat)
    (Finsupp.subtypeDomain IsDiagonalTriple A)

@[simp]
theorem diagonalBlockFinsupp_apply
    {R : Type*} [Semiring R] (A : TripleBlock R) (n : ℕ) :
    diagonalBlockFinsupp A n = A ⟨n, n, n⟩ := by
  simp [diagonalBlockFinsupp, diagonalTripleEquivNat,
    Finsupp.domCongr_apply, Finsupp.subtypeDomain_apply]

/-- Read diagonal triple coefficients as a one-variable polynomial. -/
noncomputable def diagonalBlockPolynomial
    {R : Type*} [Semiring R] (A : TripleBlock R) : Polynomial R :=
  Polynomial.ofFinsupp (diagonalBlockFinsupp A)

@[simp]
theorem diagonalBlockPolynomial_coeff
    {R : Type*} [Semiring R] (A : TripleBlock R) (n : ℕ) :
    (diagonalBlockPolynomial A).coeff n = A ⟨n, n, n⟩ := by
  simp [diagonalBlockPolynomial]

/-- Diagonal block extraction is linear. -/
noncomputable def diagonalBlockPolynomialLinear
    (R : Type*) [Semiring R] : TripleBlock R →ₗ[R] Polynomial R where
  toFun := diagonalBlockPolynomial
  map_add' := by
    intro A B
    ext n
    simp
  map_smul' := by
    intro c A
    ext n
    simp

/-- Frobenius-diagonal extraction on cube-coordinate arrays. -/
noncomputable def cubeCoordinateFrobeniusDiagonal
    (R : Type*) [Semiring R] :
    CubeCoordinateBlock R →ₗ[R] (Fin 3 → Polynomial R) where
  toFun w i := diagonalBlockPolynomial (w i i i)
  map_add' := by
    intro w₁ w₂
    funext i
    ext n
    simp
  map_smul' := by
    intro c w
    funext i
    ext n
    simp

@[simp]
theorem cubeCoordinateFrobeniusDiagonal_coeff
    (R : Type*) [Semiring R]
    (w : CubeCoordinateBlock R) (i : Fin 3) (n : ℕ) :
    (cubeCoordinateFrobeniusDiagonal R w i).coeff n =
      w i i i ⟨n, n, n⟩ := by
  simp [cubeCoordinateFrobeniusDiagonal]

/-- Frobenius diagonal on the genuine polynomial-vector tensor cube. -/
noncomputable def ternaryFrobeniusDiagonal :
    PolynomialVectorTensorCube (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3) :=
  (cubeCoordinateFrobeniusDiagonal (ZMod 3)).comp
    (polynomialVectorTensorCubeCoords (ZMod 3)).toLinearMap

/-- On a pure cube over `𝔽₃`, Frobenius diagonal recovers the source vector. -/
theorem ternaryFrobeniusDiagonal_pureCube
    (v : PolynomialVector3 (ZMod 3)) :
    ternaryFrobeniusDiagonal (v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v)) = v := by
  funext i
  apply Polynomial.ext
  intro n
  simp [ternaryFrobeniusDiagonal,
    cubeCoordinateFrobeniusDiagonal_coeff,
    polynomialVectorTensorCubeCoords_tmul,
    zmod3_cube]

/-- The Frobenius diagonal is surjective, witnessed by pure cubes. -/
theorem ternaryFrobeniusDiagonal_surjective :
    Function.Surjective ternaryFrobeniusDiagonal := by
  intro v
  exact ⟨v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v),
    ternaryFrobeniusDiagonal_pureCube v⟩

/-- The restriction of Frobenius diagonal to the divided-cube submodule is surjective. -/
theorem ternaryFrobeniusDiagonal_dividedCube_surjective :
    ∀ v : PolynomialVector3 (ZMod 3),
      ∃ w : PolynomialVectorTensorCube (ZMod 3),
        w ∈ dividedCubeSubmodule (ZMod 3) ∧
        ternaryFrobeniusDiagonal w = v := by
  intro v
  refine ⟨v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v), ?_, ?_⟩
  · exact Submodule.subset_span (Set.mem_range_self v)
  · exact ternaryFrobeniusDiagonal_pureCube v

end LeanMathlib.Rigidity
