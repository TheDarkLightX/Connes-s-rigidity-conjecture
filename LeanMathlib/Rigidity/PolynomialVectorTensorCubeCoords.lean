import Mathlib
import LeanMathlib.Rigidity.PolynomialTensorCubeBasis
import LeanMathlib.Rigidity.SymmetricCubeCoordinateOrbit

namespace LeanMathlib.Rigidity

/-- Rank-three polynomial module. -/
abbrev PolynomialVector3 (F : Type*) [Field F] := Fin 3 → Polynomial F

/-- Genuine third tensor power, right associated. -/
abbrev PolynomialVectorTensorCube (F : Type*) [Field F] :=
  TensorProduct F (PolynomialVector3 F)
    (TensorProduct F (PolynomialVector3 F) (PolynomialVector3 F))

/-- Coordinates of the tensor square of the rank-three polynomial module. -/
noncomputable def polynomialVectorPairCoords
    (F : Type*) [Field F] :
    TensorProduct F (PolynomialVector3 F) (PolynomialVector3 F) ≃ₗ[F]
      Fin 3 → Fin 3 → TensorProduct F (Polynomial F) (Polynomial F) :=
  (TensorProduct.piLeft F (PolynomialVector3 F)
      (fun _ : Fin 3 => Polynomial F)).trans
    (LinearEquiv.piCongrRight fun _ : Fin 3 =>
      TensorProduct.piRight F F (Polynomial F)
        (fun _ : Fin 3 => Polynomial F))

/-- Expand the right tensor-square factor while retaining the first polynomial factor. -/
noncomputable def polynomialRightPairCoords
    (F : Type*) [Field F] :
    TensorProduct F (Polynomial F)
      (TensorProduct F (PolynomialVector3 F) (PolynomialVector3 F)) ≃ₗ[F]
      Fin 3 → Fin 3 → PolynomialTensorCube F :=
  (TensorProduct.congr (LinearEquiv.refl F (Polynomial F))
      (polynomialVectorPairCoords F)).trans <|
    (TensorProduct.piRight F F (Polynomial F)
      (fun _ : Fin 3 =>
        Fin 3 → TensorProduct F (Polynomial F) (Polynomial F))).trans <|
      (LinearEquiv.piCongrRight fun _ : Fin 3 =>
        TensorProduct.piRight F F (Polynomial F)
          (fun _ : Fin 3 =>
            TensorProduct F (Polynomial F) (Polynomial F)))

/-- Genuine tensor-cube coordinates with triple polynomial tensor blocks. -/
noncomputable def polynomialVectorTensorCubeBlockCoords
    (F : Type*) [Field F] :
    PolynomialVectorTensorCube F ≃ₗ[F]
      Fin 3 → Fin 3 → Fin 3 → PolynomialTensorCube F :=
  (TensorProduct.piLeft F
      (TensorProduct F (PolynomialVector3 F) (PolynomialVector3 F))
      (fun _ : Fin 3 => Polynomial F)).trans <|
    (LinearEquiv.piCongrRight fun _ : Fin 3 =>
      polynomialRightPairCoords F)

/-- Apply monomial coordinates to every polynomial tensor block. -/
noncomputable def polynomialVectorTensorCubeCoords
    (F : Type*) [Field F] :
    PolynomialVectorTensorCube F ≃ₗ[F] CubeCoordinateBlock F :=
  (polynomialVectorTensorCubeBlockCoords F).trans <|
    (LinearEquiv.piCongrRight fun _ : Fin 3 =>
      LinearEquiv.piCongrRight fun _ : Fin 3 =>
        LinearEquiv.piCongrRight fun _ : Fin 3 =>
          polynomialTensorCubeCoefficients F)

@[simp]
theorem polynomialVectorPairCoords_tmul
    (F : Type*) [Field F]
    (u v : PolynomialVector3 F) (i j : Fin 3) :
    polynomialVectorPairCoords F (u ⊗ₜ[F] v) i j =
      u i ⊗ₜ[F] v j := by
  rfl

@[simp]
theorem polynomialRightPairCoords_tmul
    (F : Type*) [Field F]
    (u : Polynomial F) (v z : PolynomialVector3 F)
    (j k : Fin 3) :
    polynomialRightPairCoords F (u ⊗ₜ[F] (v ⊗ₜ[F] z)) j k =
      u ⊗ₜ[F] (v j ⊗ₜ[F] z k) := by
  rfl

@[simp]
theorem polynomialVectorTensorCubeBlockCoords_tmul
    (F : Type*) [Field F]
    (u v z : PolynomialVector3 F) (i j k : Fin 3) :
    polynomialVectorTensorCubeBlockCoords F
        (u ⊗ₜ[F] (v ⊗ₜ[F] z)) i j k =
      u i ⊗ₜ[F] (v j ⊗ₜ[F] z k) := by
  rfl

/-- Pure genuine tensors have the expected coordinate coefficient formula. -/
@[simp]
theorem polynomialVectorTensorCubeCoords_tmul
    (F : Type*) [Field F]
    (u v z : PolynomialVector3 F)
    (i j k : Fin 3) (e : TripleExponent) :
    polynomialVectorTensorCubeCoords F
        (u ⊗ₜ[F] (v ⊗ₜ[F] z)) i j k e =
      (u i).coeff e.first * (v j).coeff e.second * (z k).coeff e.third := by
  simp [polynomialVectorTensorCubeCoords]

/-- Coordinate conversion reflects zero exactly. -/
theorem polynomialVectorTensorCubeCoords_ne_zero
    (F : Type*) [Field F]
    {w : PolynomialVectorTensorCube F} (hw : w ≠ 0) :
    polynomialVectorTensorCubeCoords F w ≠ 0 :=
  (polynomialVectorTensorCubeCoords F).injective.ne hw

end LeanMathlib.Rigidity
