import Mathlib

namespace LeanMathlib.Rigidity

/-- Predicted exact number of primitive rank-three polynomial vectors of length `N`. -/
def ternaryPrimitiveCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 ^ (3 * n + 3) - 3 ^ (3 * n + 1) + 2

/-- Total number of rank-three polynomial vectors truncated at length `N`. -/
def ternaryVectorCount (N : ℕ) : ℕ := 3 ^ (3 * N)

@[simp]
theorem ternaryPrimitiveCount_succ (n : ℕ) :
    ternaryPrimitiveCount (n + 1) =
      3 ^ (3 * n + 3) - 3 ^ (3 * n + 1) + 2 := rfl

@[simp]
theorem ternaryVectorCount_succ (n : ℕ) :
    ternaryVectorCount (n + 1) = 3 ^ (3 * n + 3) := by
  simp [ternaryVectorCount]

/-- The predicted nonprimitive count is `3^(3n+1)-2`. -/
theorem ternary_nonprimitive_count (n : ℕ) :
    ternaryVectorCount (n + 1) - ternaryPrimitiveCount (n + 1) =
      3 ^ (3 * n + 1) - 2 := by
  rw [ternaryVectorCount_succ, ternaryPrimitiveCount_succ]
  have hpow : 3 ^ (3 * n + 1) ≤ 3 ^ (3 * n + 3) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Exact finite-size correction to the limiting primitive density `8/9`. -/
theorem ternary_primitive_density_identity (n : ℕ) :
    9 * ternaryPrimitiveCount (n + 1) =
      8 * ternaryVectorCount (n + 1) + 18 := by
  rw [ternaryVectorCount_succ, ternaryPrimitiveCount_succ]
  have hpow : 3 ^ (3 * n + 3) = 9 * 3 ^ (3 * n + 1) := by
    calc
      3 ^ (3 * n + 3) = 3 ^ ((3 * n + 1) + 2) := by congr 1 <;> omega
      _ = 3 ^ (3 * n + 1) * 3 ^ 2 := by rw [pow_add]
      _ = 9 * 3 ^ (3 * n + 1) := by ring
  rw [hpow]
  have hle : 3 ^ (3 * n + 1) ≤ 9 * 3 ^ (3 * n + 1) := by omega
  omega

/-- Primitive density is strictly larger than `8/9` at every finite level. -/
theorem ternary_primitive_density_gt_eight_ninths (n : ℕ) :
    8 * ternaryVectorCount (n + 1) <
      9 * ternaryPrimitiveCount (n + 1) := by
  rw [ternary_primitive_density_identity]
  omega

/-- Exact finite-size correction to the limiting nonprimitive density `1/9`. -/
theorem ternary_nonprimitive_density_identity (n : ℕ) :
    9 * (ternaryVectorCount (n + 1) -
      ternaryPrimitiveCount (n + 1)) + 18 =
        ternaryVectorCount (n + 1) := by
  rw [ternary_nonprimitive_count, ternaryVectorCount_succ]
  have hpow : 3 ^ (3 * n + 3) = 9 * 3 ^ (3 * n + 1) := by
    calc
      3 ^ (3 * n + 3) = 3 ^ ((3 * n + 1) + 2) := by congr 1 <;> omega
      _ = 3 ^ (3 * n + 1) * 3 ^ 2 := by rw [pow_add]
      _ = 9 * 3 ^ (3 * n + 1) := by ring
  rw [hpow]
  have hthree : 3 ≤ 3 ^ (3 * n + 1) := by
    calc
      3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (3 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ≤ 3 ^ (3 * n + 1) :=
    le_trans (by norm_num) hthree
  omega

/-- Nonprimitive density is strictly below `1/9` at every finite level. -/
theorem ternary_nonprimitive_density_lt_one_ninth (n : ℕ) :
    9 * (ternaryVectorCount (n + 1) -
      ternaryPrimitiveCount (n + 1)) <
        ternaryVectorCount (n + 1) := by
  have h := ternary_nonprimitive_density_identity n
  omega

end LeanMathlib.Rigidity
