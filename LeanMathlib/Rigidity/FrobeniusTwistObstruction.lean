import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

namespace LeanMathlib.Rigidity

/--
An `F`-linear retraction of the scalar cube map can exist only when the
Frobenius cube is the identity on `F`.

This is the one-dimensional obstruction behind the need for a Frobenius
twist in any characteristic-three map advertised by the formula
`d(v ⊗ v ⊗ v) = v` over a general field.
-/
theorem linear_cube_retraction_forces_frobenius_fixed
    {F : Type*} [Field F]
    (d : F →ₗ[F] F)
    (hretract : ∀ x : F, d (x ^ 3) = x)
    (x : F) :
    x ^ 3 = x := by
  have hone : d 1 = 1 := by
    simpa using hretract 1
  have hlinear : d (x ^ 3) = x ^ 3 * d 1 := by
    simpa [smul_eq_mul] using d.map_smul (x ^ 3) (1 : F)
  rw [hone, mul_one] at hlinear
  exact hlinear.symm.trans (hretract x)

/-- A scalar not fixed by Frobenius rules out an untwisted linear cube retraction. -/
theorem no_linear_cube_retraction_of_not_frobenius_fixed
    {F : Type*} [Field F]
    (x : F) (hx : x ^ 3 ≠ x) :
    ¬ ∃ d : F →ₗ[F] F, ∀ y : F, d (y ^ 3) = y := by
  rintro ⟨d, hd⟩
  exact hx (linear_cube_retraction_forces_frobenius_fixed d hd x)

end LeanMathlib.Rigidity
