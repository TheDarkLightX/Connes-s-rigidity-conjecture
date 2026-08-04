import Mathlib
import LeanMathlib.Rigidity.SingleShiftOrbit

namespace LeanMathlib.Rigidity

/-- A rank-three tensor cube represented by coordinate coefficient blocks. -/
abbrev CubeCoordinateBlock (F : Type*) [Zero F] :=
  Fin 3 → Fin 3 → Fin 3 → TripleBlock F

/-- Shift both the first and second polynomial exponents by `n`. -/
def doubleShiftTerm
    {F : Type*} [Zero F] (n : ℕ) (A : TripleBlock F) : TripleBlock F :=
  (A.embDomain (TripleExponent.shiftFirst n)).embDomain
    (TripleExponent.shiftSecond n)

/--
Coordinate formula for a transvection acting in the first two tensor slots,
when the third output coordinate is different from the transvection target.
The omitted third-slot terms are then identically absent.
-/
def firstTwoTransvectionOutput
    {F : Type*} [AddGroup F]
    (target source : Fin 3) (n : ℕ)
    (w : CubeCoordinateBlock F)
    (a b c : Fin 3) : TripleBlock F :=
  w a b c +
    (if a = target then singleShiftTerm n (w source b c) else 0) +
    (if b = target then negativeShiftTerm n (w a source c) else 0) +
    (if a = target ∧ b = target then doubleShiftTerm n (w source source c) else 0)

/-- Adding a fixed block does not destroy injectivity of a shifted family. -/
theorem const_add_singleShift_injective
    {F : Type*} [AddGroup F]
    (base A : TripleBlock F) (hA : A ≠ 0) :
    Function.Injective (fun n : ℕ => base + singleShiftTerm n A) := by
  intro m n hmn
  apply singleShiftTerm_injective A hA
  exact add_left_cancel hmn

/--
Fresh-coordinate branch: when the transvection target is absent from the
source coordinate triple, the observed output is a fixed block plus one
single-shifted nonzero block, hence is injective in the shift.
-/
theorem freshCoordinate_output_injective
    {F : Type*} [AddGroup F]
    (w : CubeCoordinateBlock F)
    (target source b c : Fin 3)
    (htb : target ≠ b) (htc : target ≠ c)
    (hsource : w source b c ≠ 0) :
    Function.Injective (fun n : ℕ =>
      firstTwoTransvectionOutput target source n w target b c) := by
  have hout (n : ℕ) :
      firstTwoTransvectionOutput target source n w target b c =
        w target b c + singleShiftTerm n (w source b c) := by
    simp [firstTwoTransvectionOutput, htb, htc]
  intro m n hmn
  apply const_add_singleShift_injective (w target b c) (w source b c) hsource
  simpa only [hout] using hmn

/-- The fresh-coordinate observed output has infinite range. -/
theorem freshCoordinate_output_infinite
    {F : Type*} [AddGroup F]
    (w : CubeCoordinateBlock F)
    (target source b c : Fin 3)
    (htb : target ≠ b) (htc : target ≠ c)
    (hsource : w source b c ≠ 0) :
    (Set.range fun n : ℕ =>
      firstTwoTransvectionOutput target source n w target b c).Infinite :=
  Set.infinite_range_of_injective
    (freshCoordinate_output_injective w target source b c htb htc hsource)

/-- Vanishing of every coordinate block with a repeated coordinate label. -/
def RepeatedCoordinateBlocksZero
    {F : Type*} [Zero F] (w : CubeCoordinateBlock F) : Prop :=
  ∀ a b c, (a = b ∨ a = c ∨ b = c) → w a b c = 0

/-- Symmetry under interchange of the first two tensor slots. -/
def SwapFirstTwoSymmetric
    {F : Type*} [Zero F] (w : CubeCoordinateBlock F) : Prop :=
  ∀ a b c, w b a c = swapFirstSecondBlock (w a b c)

/--
All-distinct branch: under repeated-block vanishing and tensor symmetry, the
repeated-coordinate output is exactly the two-term shifted block previously
proved to have an infinite tail.
-/
theorem allDistinct_output_eq
    {F : Type*} [AddGroup F]
    (w : CubeCoordinateBlock F)
    (hzero : RepeatedCoordinateBlocksZero w)
    (hsym : SwapFirstTwoSymmetric w)
    (i j k : Fin 3) :
    ∀ n : ℕ,
      firstTwoTransvectionOutput i j n w i i k =
        allDistinctShiftOutput n (w i j k) := by
  intro n
  have hbase : w i i k = 0 := hzero i i k (Or.inl rfl)
  have hdouble : w j j k = 0 := hzero j j k (Or.inl rfl)
  have hswap : w j i k = swapFirstSecondBlock (w i j k) := hsym i j k
  simp [firstTwoTransvectionOutput, hbase, hdouble, hswap,
    allDistinctShiftOutput, positiveShiftTerm, singleShiftTerm]

/-- Every nonzero all-distinct source block yields an infinite output tail. -/
theorem allDistinct_output_tail_infinite
    {F : Type*} [AddGroup F]
    (w : CubeCoordinateBlock F)
    (hzero : RepeatedCoordinateBlocksZero w)
    (hsym : SwapFirstTwoSymmetric w)
    (i j k : Fin 3)
    (hsource : w i j k ≠ 0) :
    ∃ N : ℕ,
      (Set.range fun n : ℕ =>
        firstTwoTransvectionOutput i j (N + n) w i i k).Infinite := by
  obtain ⟨N, hinfinite⟩ :=
    exists_allDistinctShiftOutput_tail_infinite (w i j k) hsource
  refine ⟨N, ?_⟩
  have heq :
      (fun n : ℕ => firstTwoTransvectionOutput i j (N + n) w i i k) =
        (fun n : ℕ => allDistinctShiftOutput (N + n) (w i j k)) := by
    funext n
    exact allDistinct_output_eq w hzero hsym i j k (N + n)
  rw [heq]
  exact hinfinite

end LeanMathlib.Rigidity
