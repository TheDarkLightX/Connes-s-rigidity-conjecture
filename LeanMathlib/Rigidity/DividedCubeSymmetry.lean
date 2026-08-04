import Mathlib
import LeanMathlib.Rigidity.PolynomialVectorTensorCubeCoords

namespace LeanMathlib.Rigidity

/-- Evaluate a first/second variable swap by swapping the exponent coordinates. -/
@[simp]
theorem swapFirstSecondBlock_apply
    {F : Type*} [Zero F]
    (A : TripleBlock F) (e : TripleExponent) :
    swapFirstSecondBlock A e = A (TripleExponent.swapFirstSecond e) := by
  have h := Finsupp.embDomain_apply_self
    TripleExponent.swapFirstSecond.toEmbedding A
    (TripleExponent.swapFirstSecond e)
  simpa [swapFirstSecondBlock] using h

@[simp]
theorem swapFirstSecondBlock_zero
    {F : Type*} [Zero F] :
    swapFirstSecondBlock (0 : TripleBlock F) = 0 := by
  ext e
  simp

@[simp]
theorem swapFirstSecondBlock_add
    {F : Type*} [AddZeroClass F]
    (A B : TripleBlock F) :
    swapFirstSecondBlock (A + B) =
      swapFirstSecondBlock A + swapFirstSecondBlock B := by
  ext e
  simp

@[simp]
theorem swapFirstSecondBlock_smul
    {F : Type*} [Semiring F]
    (c : F) (A : TripleBlock F) :
    swapFirstSecondBlock (c • A) = c • swapFirstSecondBlock A := by
  ext e
  simp

/-- Swap the first two genuine tensor factors. -/
noncomputable def swapFirstTwoTensorCube
    (F : Type*) [Field F] :
    PolynomialVectorTensorCube F ≃ₗ[F] PolynomialVectorTensorCube F :=
  TensorProduct.leftComm F
    (PolynomialVector3 F) (PolynomialVector3 F) (PolynomialVector3 F)

@[simp]
theorem swapFirstTwoTensorCube_tmul
    (F : Type*) [Field F]
    (u v z : PolynomialVector3 F) :
    swapFirstTwoTensorCube F (u ⊗ₜ[F] (v ⊗ₜ[F] z)) =
      v ⊗ₜ[F] (u ⊗ₜ[F] z) := by
  rfl

/-- Coordinate conversion intertwines genuine factor swap and exponent-variable swap. -/
theorem polynomialVectorTensorCubeCoords_swapFirstTwo
    (F : Type*) [Field F]
    (w : PolynomialVectorTensorCube F)
    (i j k : Fin 3) :
    polynomialVectorTensorCubeCoords F (swapFirstTwoTensorCube F w) i j k =
      swapFirstSecondBlock
        (polynomialVectorTensorCubeCoords F w j i k) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul u q =>
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul v z =>
          ext e
          simp [mul_assoc, mul_left_comm, mul_comm]

/-- A tensor fixed by the first-factor transposition has symmetric coordinates. -/
theorem fixed_swapFirstTwo_coords_symmetric
    (F : Type*) [Field F]
    {w : PolynomialVectorTensorCube F}
    (hfixed : swapFirstTwoTensorCube F w = w) :
    SwapFirstTwoSymmetric (polynomialVectorTensorCubeCoords F w) := by
  intro i j k
  have hswap :=
    polynomialVectorTensorCubeCoords_swapFirstTwo F w j i k
  rw [hfixed] at hswap
  exact hswap

/-- The span of pure cubes in the genuine tensor cube. -/
noncomputable def dividedCubeSubmodule
    (F : Type*) [Field F] :
    Submodule F (PolynomialVectorTensorCube F) :=
  Submodule.span F
    (Set.range fun v : PolynomialVector3 F => v ⊗ₜ[F] (v ⊗ₜ[F] v))

/-- Every divided-cube tensor is fixed by swapping the first two factors. -/
theorem dividedCube_fixed_swapFirstTwo
    (F : Type*) [Field F]
    {w : PolynomialVectorTensorCube F}
    (hw : w ∈ dividedCubeSubmodule F) :
    swapFirstTwoTensorCube F w = w := by
  refine Submodule.span_induction hw ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro c x hx
    simp [map_smul, hx]

/-- Genuine divided cubes satisfy the coordinate symmetry used by the rank-three orbit theorem. -/
theorem dividedCube_coords_swapFirstTwoSymmetric
    (F : Type*) [Field F]
    {w : PolynomialVectorTensorCube F}
    (hw : w ∈ dividedCubeSubmodule F) :
    SwapFirstTwoSymmetric (polynomialVectorTensorCubeCoords F w) := by
  exact fixed_swapFirstTwo_coords_symmetric F
    (dividedCube_fixed_swapFirstTwo F hw)

end LeanMathlib.Rigidity
