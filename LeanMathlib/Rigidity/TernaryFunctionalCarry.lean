import Mathlib
import LeanMathlib.Rigidity.AbelianCocycleExtension
import LeanMathlib.Rigidity.TernaryWittCarry
import LeanMathlib.Rigidity.DividedCubeSymmetry

namespace LeanMathlib.Rigidity

/-- Algebraic dual of the rank-three polynomial module. -/
abbrev PolynomialVectorDual :=
  Module.Dual (ZMod 3) (PolynomialVector3 (ZMod 3))

/-- Algebraic dual of the ternary divided-cube module. -/
abbrev DividedCubeDual :=
  Module.Dual (ZMod 3) (dividedCubeSubmodule (ZMod 3))

/--
Ordered tensor representative of the ternary carry polynomial. On a pure cube
it evaluates to `C₃(ℓ(v), m(v))`.
-/
noncomputable def ternaryCarryTensorFunctional
    (ell m : PolynomialVectorDual) :
    PolynomialVectorTensorCube (ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  TensorProduct.lift
    { toFun := fun u =>
        TensorProduct.lift
          { toFun := fun v =>
              { toFun := fun z =>
                  -(ell u * ell v * m z + ell u * m v * m z)
                map_add' := by intro x y; simp; ring
                map_smul' := by intro c x; simp; ring }
            map_add' := by
              intro x y
              ext z
              simp
              ring
            map_smul' := by
              intro c x
              ext z
              simp
              ring }
      map_add' := by
        intro x y
        ext q
        induction q using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp [ha, hb]
        | tmul v z => simp; ring
      map_smul' := by
        intro c x
        ext q
        induction q using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp [ha, hb]
        | tmul v z => simp; ring }

@[simp]
theorem ternaryCarryTensorFunctional_tmul
    (ell m : PolynomialVectorDual)
    (u v z : PolynomialVector3 (ZMod 3)) :
    ternaryCarryTensorFunctional ell m (u ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] z)) =
      -(ell u * ell v * m z + ell u * m v * m z) := by
  simp [ternaryCarryTensorFunctional]

/-- Restrict the tensor representative to the divided-cube submodule. -/
noncomputable def ternaryFunctionalCarry
    (ell m : PolynomialVectorDual) : DividedCubeDual :=
  (ternaryCarryTensorFunctional ell m).comp
    (dividedCubeSubmodule (ZMod 3)).subtype

@[simp]
theorem ternaryFunctionalCarry_pureCube
    (ell m : PolynomialVectorDual)
    (v : PolynomialVector3 (ZMod 3)) :
    ternaryFunctionalCarry ell m
      ⟨v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v),
        Submodule.subset_span (Set.mem_range_self v)⟩ =
      ternaryCarry (ell v) (m v) := by
  simp [ternaryFunctionalCarry, ternaryCarry]
  ring

@[simp]
theorem ternaryFunctionalCarry_zero_left
    (ell : PolynomialVectorDual) :
    ternaryFunctionalCarry 0 ell = 0 := by
  ext b
  rcases b with ⟨w, hw⟩
  change ternaryCarryTensorFunctional 0 ell w = 0
  refine Submodule.span_induction hw ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro c x hx
    simp [map_smul, hx]

/-- Symmetry holds on the divided-cube span. -/
theorem ternaryFunctionalCarry_comm
    (ell m : PolynomialVectorDual) :
    ternaryFunctionalCarry ell m = ternaryFunctionalCarry m ell := by
  ext b
  rcases b with ⟨w, hw⟩
  change ternaryCarryTensorFunctional ell m w =
    ternaryCarryTensorFunctional m ell w
  refine Submodule.span_induction hw ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simpa using ternaryCarry_comm (ell v) (m v)
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro c x hx
    simp [map_smul, hx]

/-- The scalar cocycle identity lifts to the divided-cube dual. -/
theorem ternaryFunctionalCarry_cocycle
    (ell m d : PolynomialVectorDual) :
    ternaryFunctionalCarry ell m + ternaryFunctionalCarry (ell + m) d =
      ternaryFunctionalCarry m d + ternaryFunctionalCarry ell (m + d) := by
  ext b
  rcases b with ⟨w, hw⟩
  change
    ternaryCarryTensorFunctional ell m w +
        ternaryCarryTensorFunctional (ell + m) d w =
      ternaryCarryTensorFunctional m d w +
        ternaryCarryTensorFunctional ell (m + d) w
  refine Submodule.span_induction hw ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simpa using ternaryCarry_cocycle (ell v) (m v) (d v)
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro c x hx
    simp [map_smul, hx]

/-- Ternary functional carry as normalized symmetric additive cocycle data. -/
noncomputable def ternaryFunctionalCarryCocycle :
    NormalizedSymmetricAddCocycle PolynomialVectorDual DividedCubeDual where
  c := ternaryFunctionalCarry
  zero_left := ternaryFunctionalCarry_zero_left
  symmetric := ternaryFunctionalCarry_comm
  cocycle := ternaryFunctionalCarry_cocycle

/-- The unshifted compact-dual carry group, algebraically. -/
abbrev TernaryFunctionalCarryExtension :=
  ternaryFunctionalCarryCocycle.Extension

end LeanMathlib.Rigidity
