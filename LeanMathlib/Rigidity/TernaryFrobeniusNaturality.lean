import Mathlib
import LeanMathlib.Rigidity.TernaryFrobeniusDiagonal
import LeanMathlib.Rigidity.PolynomialTensorCubeTransvection

namespace LeanMathlib.Rigidity

/-- Diagonal tensor-cube action of a linear endomorphism. -/
noncomputable def tensorCubeMap
    {F : Type*} [Field F]
    (L : PolynomialVector3 F →ₗ[F] PolynomialVector3 F) :
    PolynomialVectorTensorCube F →ₗ[F] PolynomialVectorTensorCube F :=
  TensorProduct.map L (TensorProduct.map L L)

@[simp]
theorem tensorCubeMap_pureCube
    {F : Type*} [Field F]
    (L : PolynomialVector3 F →ₗ[F] PolynomialVector3 F)
    (v : PolynomialVector3 F) :
    tensorCubeMap L (v ⊗ₜ[F] (v ⊗ₜ[F] v)) =
      L v ⊗ₜ[F] (L v ⊗ₜ[F] L v) := by
  simp [tensorCubeMap]

/-- Every linear endomorphism preserves the divided-cube submodule. -/
theorem tensorCubeMap_mem_dividedCube
    {F : Type*} [Field F]
    (L : PolynomialVector3 F →ₗ[F] PolynomialVector3 F)
    {w : PolynomialVectorTensorCube F}
    (hw : w ∈ dividedCubeSubmodule F) :
    tensorCubeMap L w ∈ dividedCubeSubmodule F := by
  refine Submodule.span_induction
    (p := fun x _ => tensorCubeMap L x ∈ dividedCubeSubmodule F)
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    rw [tensorCubeMap_pureCube]
    exact Submodule.subset_span (Set.mem_range_self (L v))
  · change tensorCubeMap L 0 ∈ dividedCubeSubmodule F
    rw [(tensorCubeMap L).map_zero]
    exact (dividedCubeSubmodule F).zero_mem
  · intro x y hx hy hLx hLy
    rw [(tensorCubeMap L).map_add]
    exact (dividedCubeSubmodule F).add_mem hLx hLy
  · intro c x hx hLx
    rw [(tensorCubeMap L).map_smul]
    exact (dividedCubeSubmodule F).smul_mem c hLx

/--
On divided cubes, the ternary Frobenius diagonal intertwines every
`𝔽₃`-linear endomorphism with its diagonal tensor-cube action.
-/
theorem ternaryFrobeniusDiagonal_natural
    (L : PolynomialVector3 (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3))
    {w : PolynomialVectorTensorCube (ZMod 3)}
    (hw : w ∈ dividedCubeSubmodule (ZMod 3)) :
    ternaryFrobeniusDiagonal (tensorCubeMap L w) =
      L (ternaryFrobeniusDiagonal w) := by
  refine Submodule.span_induction
    (p := fun x _ =>
      ternaryFrobeniusDiagonal (tensorCubeMap L x) =
        L (ternaryFrobeniusDiagonal x))
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp [tensorCubeMap_pureCube, ternaryFrobeniusDiagonal_pureCube]
  · change ternaryFrobeniusDiagonal (tensorCubeMap L 0) =
      L (ternaryFrobeniusDiagonal 0)
    rw [(tensorCubeMap L).map_zero,
      ternaryFrobeniusDiagonal.map_zero,
      ternaryFrobeniusDiagonal.map_zero, L.map_zero]
  · intro x y hx hy hnatX hnatY
    rw [(tensorCubeMap L).map_add,
      ternaryFrobeniusDiagonal.map_add,
      ternaryFrobeniusDiagonal.map_add, L.map_add, hnatX, hnatY]
  · intro c x hx hnat
    rw [(tensorCubeMap L).map_smul,
      ternaryFrobeniusDiagonal.map_smul,
      ternaryFrobeniusDiagonal.map_smul, L.map_smul, hnat]

/-- The actual polynomial transvection action preserves divided cubes. -/
theorem polynomialSLTensorCubeAction_mem_dividedCube
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ)
    {w : PolynomialVectorTensorCube (ZMod 3)}
    (hw : w ∈ dividedCubeSubmodule (ZMod 3)) :
    polynomialSLTensorCubeAction (ZMod 3) target source hts n w ∈
      dividedCubeSubmodule (ZMod 3) := by
  rw [polynomialSLTensorCubeAction_eq]
  exact tensorCubeMap_mem_dividedCube
    (polynomialVectorTransvection (ZMod 3) target source n) hw

/-- Frobenius diagonal is equivariant for actual `SL₃(𝔽₃[t])` transvections. -/
theorem ternaryFrobeniusDiagonal_transvection
    (target source : Fin 3) (hts : target ≠ source) (n : ℕ)
    {w : PolynomialVectorTensorCube (ZMod 3)}
    (hw : w ∈ dividedCubeSubmodule (ZMod 3)) :
    ternaryFrobeniusDiagonal
        (polynomialSLTensorCubeAction (ZMod 3) target source hts n w) =
      polynomialVectorTransvection (ZMod 3) target source n
        (ternaryFrobeniusDiagonal w) := by
  rw [polynomialSLTensorCubeAction_eq]
  exact ternaryFrobeniusDiagonal_natural
    (polynomialVectorTransvection (ZMod 3) target source n) hw

end LeanMathlib.Rigidity
