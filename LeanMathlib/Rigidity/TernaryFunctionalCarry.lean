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

/-- Evaluate a tensor by a pair of scalar-valued linear maps. -/
noncomputable def tensorProductScalarEval
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] R) (g : N →ₗ[R] R) :
    TensorProduct R M N →ₗ[R] R :=
  TensorProduct.lift
    { toFun := fun x => (f x) • g
      map_add' := by
        intro x y
        ext z
        simp [add_mul]
      map_smul' := by
        intro c x
        ext z
        simp [mul_assoc] }

@[simp]
theorem tensorProductScalarEval_tmul
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] R) (g : N →ₗ[R] R) (x : M) (y : N) :
    tensorProductScalarEval f g (x ⊗ₜ[R] y) = f x * g y := by
  simp [tensorProductScalarEval]

/--
Ordered tensor representative of the ternary carry polynomial. On a pure cube
it evaluates to `C₃(ℓ(v), m(v))`.
-/
noncomputable def ternaryCarryTensorFunctional
    (ell m : PolynomialVectorDual) :
    PolynomialVectorTensorCube (ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  -(tensorProductScalarEval ell
    (tensorProductScalarEval ell m + tensorProductScalarEval m m))

@[simp]
theorem ternaryCarryTensorFunctional_tmul
    (ell m : PolynomialVectorDual)
    (u v z : PolynomialVector3 (ZMod 3)) :
    ternaryCarryTensorFunctional ell m (u ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] z)) =
      -(ell u * ell v * m z + ell u * m v * m z) := by
  simp [ternaryCarryTensorFunctional]
  ring

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
  refine Submodule.span_induction
    (p := fun x _ => ternaryCarryTensorFunctional 0 ell x = 0)
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp
  · exact (ternaryCarryTensorFunctional 0 ell).map_zero
  · intro x y hx hy hzeroX hzeroY
    rw [(ternaryCarryTensorFunctional 0 ell).map_add, hzeroX, hzeroY,
      add_zero]
  · intro c x hx hzero
    rw [(ternaryCarryTensorFunctional 0 ell).map_smul, hzero, smul_zero]

/-- Symmetry holds on the divided-cube span. -/
theorem ternaryFunctionalCarry_comm
    (ell m : PolynomialVectorDual) :
    ternaryFunctionalCarry ell m = ternaryFunctionalCarry m ell := by
  ext b
  rcases b with ⟨w, hw⟩
  change ternaryCarryTensorFunctional ell m w =
    ternaryCarryTensorFunctional m ell w
  refine Submodule.span_induction
    (p := fun x _ => ternaryCarryTensorFunctional ell m x =
      ternaryCarryTensorFunctional m ell x)
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp
    ring
  · simp
  · intro x y hx hy hcommX hcommY
    rw [(ternaryCarryTensorFunctional ell m).map_add,
      (ternaryCarryTensorFunctional m ell).map_add, hcommX, hcommY]
  · intro c x hx hcomm
    rw [(ternaryCarryTensorFunctional ell m).map_smul,
      (ternaryCarryTensorFunctional m ell).map_smul, hcomm]

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
  refine Submodule.span_induction
    (p := fun x _ =>
      ternaryCarryTensorFunctional ell m x +
          ternaryCarryTensorFunctional (ell + m) d x =
        ternaryCarryTensorFunctional m d x +
          ternaryCarryTensorFunctional ell (m + d) x)
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    simp
    ring
  · simp
  · intro x y hx hy hcocycleX hcocycleY
    rw [(ternaryCarryTensorFunctional ell m).map_add,
      (ternaryCarryTensorFunctional (ell + m) d).map_add,
      (ternaryCarryTensorFunctional m d).map_add,
      (ternaryCarryTensorFunctional ell (m + d)).map_add]
    calc
      (ternaryCarryTensorFunctional ell m x +
            ternaryCarryTensorFunctional ell m y) +
          (ternaryCarryTensorFunctional (ell + m) d x +
            ternaryCarryTensorFunctional (ell + m) d y) =
          (ternaryCarryTensorFunctional ell m x +
              ternaryCarryTensorFunctional (ell + m) d x) +
            (ternaryCarryTensorFunctional ell m y +
              ternaryCarryTensorFunctional (ell + m) d y) := by abel
      _ = (ternaryCarryTensorFunctional m d x +
              ternaryCarryTensorFunctional ell (m + d) x) +
            (ternaryCarryTensorFunctional m d y +
              ternaryCarryTensorFunctional ell (m + d) y) := by
            rw [hcocycleX, hcocycleY]
      _ = (ternaryCarryTensorFunctional m d x +
            ternaryCarryTensorFunctional m d y) +
          (ternaryCarryTensorFunctional ell (m + d) x +
            ternaryCarryTensorFunctional ell (m + d) y) := by abel
  · intro c x hx hcocycle
    rw [(ternaryCarryTensorFunctional ell m).map_smul,
      (ternaryCarryTensorFunctional (ell + m) d).map_smul,
      (ternaryCarryTensorFunctional m d).map_smul,
      (ternaryCarryTensorFunctional ell (m + d)).map_smul]
    rw [← smul_add, ← smul_add, hcocycle]

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
