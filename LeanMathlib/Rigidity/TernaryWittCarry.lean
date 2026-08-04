import Mathlib

namespace LeanMathlib.Rigidity

/-- The length-two ternary Witt carry polynomial. -/
def ternaryCarry {R : Type*} [CommRing R] (x y : R) : R :=
  -(x ^ 2 * y + x * y ^ 2)

@[simp]
theorem ternaryCarry_zero_left {R : Type*} [CommRing R] (x : R) :
    ternaryCarry 0 x = 0 := by
  simp [ternaryCarry]

@[simp]
theorem ternaryCarry_zero_right {R : Type*} [CommRing R] (x : R) :
    ternaryCarry x 0 = 0 := by
  simp [ternaryCarry]

/-- The ternary carry is symmetric. -/
theorem ternaryCarry_comm {R : Type*} [CommRing R] (x y : R) :
    ternaryCarry x y = ternaryCarry y x := by
  simp [ternaryCarry]
  ring

/-- The scalar cocycle identity underlying associativity of ternary Witt addition. -/
theorem ternaryCarry_cocycle {R : Type*} [CommRing R] (x y z : R) :
    ternaryCarry x y + ternaryCarry (x + y) z =
      ternaryCarry y z + ternaryCarry x (y + z) := by
  simp [ternaryCarry]
  ring

/-- Length-two ternary Witt addition written in carry coordinates. -/
def ternaryWittAdd {R : Type*} [CommRing R]
    (u v : R × R) : R × R :=
  (u.1 + v.1, u.2 + v.2 + ternaryCarry u.1 v.1)

@[simp]
theorem ternaryWittAdd_zero_left {R : Type*} [CommRing R] (u : R × R) :
    ternaryWittAdd (0, 0) u = u := by
  ext <;> simp [ternaryWittAdd]

@[simp]
theorem ternaryWittAdd_zero_right {R : Type*} [CommRing R] (u : R × R) :
    ternaryWittAdd u (0, 0) = u := by
  ext <;> simp [ternaryWittAdd]

/-- Carry-coordinate ternary Witt addition is commutative. -/
theorem ternaryWittAdd_comm {R : Type*} [CommRing R] (u v : R × R) :
    ternaryWittAdd u v = ternaryWittAdd v u := by
  ext <;> simp [ternaryWittAdd, ternaryCarry] <;> ring

/-- Carry-coordinate ternary Witt addition is associative. -/
theorem ternaryWittAdd_assoc {R : Type*} [CommRing R] (u v w : R × R) :
    ternaryWittAdd (ternaryWittAdd u v) w =
      ternaryWittAdd u (ternaryWittAdd v w) := by
  ext <;> simp [ternaryWittAdd, ternaryCarry] <;> ring

/-- Frobenius is the identity on the prime field `ZMod 3`. -/
theorem zmod3_cube (x : ZMod 3) : x ^ 3 = x := by
  fin_cases x <;> native_decide

/--
Three copies of a first-coordinate element create one unit of second-coordinate
carry. This is the length-two identity corresponding to `3 · (a, 0) = (0, a)`
in `W₂(𝔽₃)`.
-/
theorem ternaryWittAdd_threefold (a : ZMod 3) :
    ternaryWittAdd (ternaryWittAdd (a, 0) (a, 0)) (a, 0) = (0, a) := by
  fin_cases a <;> native_decide

/-- A coordinate model for a pure third tensor power. -/
def pureCube {ι R : Type*} [CommRing R] (v : ι → R) :
    ι → ι → ι → R :=
  fun i j k => v i * v j * v k

/-- Extract the diagonal of a cubic tensor-coordinate function. -/
def cubeDiagonal {ι R : Type*} (T : ι → ι → ι → R) : ι → R :=
  fun i => T i i i

/-- On `𝔽₃`, diagonal extraction sends a pure cube back to its source vector. -/
theorem cubeDiagonal_pureCube_zmod3 {ι : Type*} (v : ι → ZMod 3) :
    cubeDiagonal (pureCube v) = v := by
  funext i
  simp [cubeDiagonal, pureCube, ← pow_succ, zmod3_cube]

end LeanMathlib.Rigidity
