import Mathlib
import LeanMathlib.Rigidity.DividedCubeSymmetry
import LeanMathlib.Rigidity.PolynomialTensorCubeTransvection

namespace LeanMathlib.Rigidity

/--
Every nonzero divided cube admits an actual `SL₃(F[t])` transvection family
whose one coordinate-block observation has infinite range.
-/
theorem dividedCube_has_infinite_SL3_observation
    (F : Type*) [Field F]
    (w : PolynomialVectorTensorCube F)
    (hwdiv : w ∈ dividedCubeSubmodule F)
    (hwne : w ≠ 0) :
    ∃ (target source out₁ out₂ out₃ : Fin 3)
      (hts : target ≠ source) (N : ℕ),
      target ≠ out₃ ∧
      (Set.range fun n : ℕ =>
        polynomialVectorTensorCubeCoords F
          (polynomialSLTensorCubeAction F target source hts (N + n) w)
          out₁ out₂ out₃).Infinite := by
  let coords := polynomialVectorTensorCubeCoords F w
  have hcoords_ne : coords ≠ 0 :=
    polynomialVectorTensorCubeCoords_ne_zero F hwne
  have hsym : SwapFirstTwoSymmetric coords :=
    dividedCube_coords_swapFirstTwoSymmetric F hwdiv
  obtain ⟨target, source, out₁, out₂, out₃, N,
      hts, htout₃, hinfinite⟩ :=
    symmetricCubeCoordinate_has_infinite_transvection_observation
      coords hcoords_ne hsym
  refine ⟨target, source, out₁, out₂, out₃, hts, N, htout₃, ?_⟩
  have heq :
      (fun n : ℕ =>
        polynomialVectorTensorCubeCoords F
          (polynomialSLTensorCubeAction F target source hts (N + n) w)
          out₁ out₂ out₃) =
      (fun n : ℕ =>
        firstTwoTransvectionOutput target source (N + n) coords
          out₁ out₂ out₃) := by
    funext n
    exact polynomialSLTensorCubeAction_coords
      F target source hts (N + n) w out₁ out₂ out₃ htout₃
  rw [heq]
  exact hinfinite

/--
Main rank-three orbit theorem: every nonzero element in the span of pure cubes
of `(F[t]^3)^{⊗3}` has an infinite orbit under actual elementary
transvections in `SL₃(F[t])`.
-/
theorem dividedCube_SL3_orbit_infinite
    (F : Type*) [Field F]
    (w : PolynomialVectorTensorCube F)
    (hwdiv : w ∈ dividedCubeSubmodule F)
    (hwne : w ≠ 0) :
    ∃ (target source : Fin 3) (hts : target ≠ source) (N : ℕ),
      (Set.range fun n : ℕ =>
        polynomialSLTensorCubeAction F target source hts (N + n) w).Infinite := by
  obtain ⟨target, source, out₁, out₂, out₃, hts, N, htout₃, hobs⟩ :=
    dividedCube_has_infinite_SL3_observation F w hwdiv hwne
  refine ⟨target, source, hts, N, ?_⟩
  let orbitTerm : ℕ → PolynomialVectorTensorCube F := fun n =>
    polynomialSLTensorCubeAction F target source hts (N + n) w
  let observe : PolynomialVectorTensorCube F → CubeCoordinateBlock F :=
    polynomialVectorTensorCubeCoords F
  let observeBlock : PolynomialVectorTensorCube F → TripleBlock F := fun x =>
    observe x out₁ out₂ out₃
  by_contra hfinite
  have horbitFinite : (Set.range orbitTerm).Finite := by
    simpa [orbitTerm] using hfinite
  have himageFinite : (observeBlock '' Set.range orbitTerm).Finite :=
    horbitFinite.image observeBlock
  apply hobs
  apply himageFinite.subset
  rintro y ⟨n, rfl⟩
  refine ⟨orbitTerm n, ⟨n, rfl⟩, ?_⟩
  rfl

end LeanMathlib.Rigidity
