import Mathlib
import LeanMathlib.Rigidity.TernaryShiftedCarry
import LeanMathlib.Rigidity.TernaryFrobeniusDiagonal

namespace LeanMathlib.Rigidity

/-- Frobenius diagonal restricted to the divided-cube module. -/
noncomputable def ternaryDividedCubeFrobeniusDiagonal :
    dividedCubeSubmodule (ZMod 3) →ₗ[ZMod 3]
      PolynomialVector3 (ZMod 3) :=
  ternaryFrobeniusDiagonal.comp (dividedCubeSubmodule (ZMod 3)).subtype

@[simp]
theorem ternaryDividedCubeFrobeniusDiagonal_pureCube
    (v : PolynomialVector3 (ZMod 3)) :
    ternaryDividedCubeFrobeniusDiagonal
      ⟨v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v),
        Submodule.subset_span (Set.mem_range_self v)⟩ = v := by
  exact ternaryFrobeniusDiagonal_pureCube v

/-- Dual of shifted Frobenius diagonal: `ℓ ↦ ℓ ∘ t^n ∘ d₃`. -/
noncomputable def ternaryShiftedFrobeniusDual (n : ℕ) :
    PolynomialVectorDual →ₗ[ZMod 3] DividedCubeDual where
  toFun ell :=
    (polynomialVectorDualShift n ell).comp
      ternaryDividedCubeFrobeniusDiagonal
  map_add' := by
    intro ell m
    ext b
    simp
  map_smul' := by
    intro c ell
    ext b
    simp

@[simp]
theorem ternaryShiftedFrobeniusDual_apply
    (n : ℕ) (ell : PolynomialVectorDual)
    (b : dividedCubeSubmodule (ZMod 3)) :
    ternaryShiftedFrobeniusDual n ell b =
      ell (polynomialVectorShift n
        (ternaryDividedCubeFrobeniusDiagonal b)) := rfl

@[simp]
theorem ternaryShiftedFrobeniusDual_pureCube
    (n : ℕ) (ell : PolynomialVectorDual)
    (v : PolynomialVector3 (ZMod 3)) :
    ternaryShiftedFrobeniusDual n ell
      ⟨v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v),
        Submodule.subset_span (Set.mem_range_self v)⟩ =
      ell (polynomialVectorShift n v) := by
  simp

/-- Scalar identity behind multiplication by three in `W₂(𝔽₃)`. -/
theorem ternaryCarry_three_identity (a : ZMod 3) :
    ternaryCarry a a + ternaryCarry (a + a) a = a := by
  fin_cases a <;> decide

/-- Three copies of a shifted carry-group element equal the shifted Frobenius dual of its base. -/
theorem ternaryShiftedCarry_three_nsmul
    (n : ℕ) (x : TernaryShiftedCarryExtension n) :
    3 • x =
      (ternaryShiftedFunctionalCarryCocycle n).fiberHom
        (ternaryShiftedFrobeniusDual n x.base) := by
  apply NormalizedSymmetricAddCocycle.Extension.ext
  · change (ternaryShiftedFunctionalCarryCocycle n).baseHom (3 • x) = 0
    rw [map_nsmul]
    exact ZModModule.char_nsmul_eq_zero 3 x.base
  · rcases x with ⟨ell, q⟩
    simp only [three_nsmul]
    change
      q + (q + q + ternaryShiftedFunctionalCarry n ell ell) +
          ternaryShiftedFunctionalCarry n ell (ell + ell) =
        ternaryShiftedFrobeniusDual n ell
    rw [ternaryShiftedFunctionalCarry_comm n ell (ell + ell)]
    have hqzero : q + q + q = 0 := by
      have hchar := ZModModule.char_nsmul_eq_zero 3 q
      rw [three_nsmul] at hchar
      calc
        q + q + q = q + (q + q) := by abel
        _ = 0 := hchar
    calc
        q + (q + q + ternaryShiftedFunctionalCarry n ell ell) +
              ternaryShiftedFunctionalCarry n (ell + ell) ell =
          (q + q + q) +
            (ternaryShiftedFunctionalCarry n ell ell +
              ternaryShiftedFunctionalCarry n (ell + ell) ell) := by
            abel
      _ = ternaryShiftedFunctionalCarry n ell ell +
            ternaryShiftedFunctionalCarry n (ell + ell) ell := by
              rw [hqzero, zero_add]
      _ = ternaryShiftedFrobeniusDual n ell := by
        apply (Submodule.linearMap_eq_iff_of_eq_span
          (ternaryShiftedFunctionalCarry n ell ell +
            ternaryShiftedFunctionalCarry n (ell + ell) ell)
          (ternaryShiftedFrobeniusDual n ell)
          (S := Set.range fun v : PolynomialVector3 (ZMod 3) =>
            v ⊗ₜ[ZMod 3] (v ⊗ₜ[ZMod 3] v)) (by rfl)).2
        rintro ⟨_, ⟨v, rfl⟩⟩
        simpa [ternaryShiftedFunctionalCarry] using
          ternaryCarry_three_identity
            (ell (polynomialVectorShift n v))

/-- Every shifted ternary carry-group element has exponent dividing nine. -/
theorem ternaryShiftedCarry_nine_nsmul
    (n : ℕ) (x : TernaryShiftedCarryExtension n) :
    9 • x = 0 := by
  rw [show 9 = 3 * 3 by norm_num, mul_nsmul,
    ternaryShiftedCarry_three_nsmul n x]
  change 3 • (ternaryShiftedFunctionalCarryCocycle n).fiberHom
      (ternaryShiftedFrobeniusDual n x.base) = 0
  rw [← map_nsmul]
  have hzero : 3 • ternaryShiftedFrobeniusDual n x.base = 0 :=
    ZModModule.char_nsmul_eq_zero 3 _
  simp [hzero]

/-- Three-torsion is characterized by the kernel of shifted Frobenius dual. -/
theorem ternaryShiftedCarry_mem_threeTorsion_iff
    (n : ℕ) (x : TernaryShiftedCarryExtension n) :
    3 • x = 0 ↔ ternaryShiftedFrobeniusDual n x.base = 0 := by
  rw [ternaryShiftedCarry_three_nsmul]
  constructor
  · intro h
    exact (ternaryShiftedFunctionalCarryCocycle n).fiberHom_injective h
  · intro h
    simp [h]

end LeanMathlib.Rigidity
