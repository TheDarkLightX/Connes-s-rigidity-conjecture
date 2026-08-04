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
  | zero =>
      rw [(swapFirstTwoTensorCube F).map_zero,
        (polynomialVectorTensorCubeCoords F).map_zero]
      simp
  | add x y hx hy =>
      rw [(swapFirstTwoTensorCube F).map_add,
        (polynomialVectorTensorCubeCoords F).map_add,
        (polynomialVectorTensorCubeCoords F).map_add]
      simp only [Pi.add_apply, swapFirstSecondBlock_add, hx, hy]
  | tmul u q =>
      induction q using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero,
            (swapFirstTwoTensorCube F).map_zero,
            (polynomialVectorTensorCubeCoords F).map_zero]
          simp
      | add x y hx hy =>
          rw [TensorProduct.tmul_add,
            (swapFirstTwoTensorCube F).map_add,
            (polynomialVectorTensorCubeCoords F).map_add,
            (polynomialVectorTensorCubeCoords F).map_add]
          simp only [Pi.add_apply, swapFirstSecondBlock_add, hx, hy]
      | tmul v z =>
          ext e
          simp [TripleExponent.swapFirstSecond, mul_assoc, mul_comm]

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
  refine Submodule.span_induction
    (p := fun x _ => swapFirstTwoTensorCube F x = x) ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    exact swapFirstTwoTensorCube_tmul F v v v
  · exact (swapFirstTwoTensorCube F).map_zero
  · intro x y hx hy hfixx hfixy
    rw [(swapFirstTwoTensorCube F).map_add, hfixx, hfixy]
  · intro c x hx hfix
    rw [(swapFirstTwoTensorCube F).map_smul, hfix]

/-- Genuine divided cubes satisfy the coordinate symmetry used by the rank-three orbit theorem. -/
theorem dividedCube_coords_swapFirstTwoSymmetric
    (F : Type*) [Field F]
    {w : PolynomialVectorTensorCube F}
    (hw : w ∈ dividedCubeSubmodule F) :
    SwapFirstTwoSymmetric (polynomialVectorTensorCubeCoords F w) := by
  intro i j k
  have hswap :=
    polynomialVectorTensorCubeCoords_swapFirstTwo F w j i k
  rw [dividedCube_fixed_swapFirstTwo F hw] at hswap
  exact hswap

end LeanMathlib.Rigidity
