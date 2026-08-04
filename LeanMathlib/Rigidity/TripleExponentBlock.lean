import Mathlib
import LeanMathlib.Rigidity.SupportOrbitCore

namespace LeanMathlib.Rigidity

/-- Exponents of a monomial in three independent polynomial variables. -/
@[ext]
structure TripleExponent where
  first : ℕ
  second : ℕ
  third : ℕ
  deriving DecidableEq

namespace TripleExponent

/-- Difference between the first and second exponents. -/
def difference (e : TripleExponent) : ℤ :=
  (e.first : ℤ) - e.second

/-- Total monomial degree. -/
def totalDegree (e : TripleExponent) : ℕ :=
  e.first + e.second + e.third

/-- Swap the first two tensor-polynomial variables. -/
def swapFirstSecond : TripleExponent ≃ TripleExponent where
  toFun e := ⟨e.second, e.first, e.third⟩
  invFun e := ⟨e.second, e.first, e.third⟩
  left_inv := by intro e; ext <;> rfl
  right_inv := by intro e; ext <;> rfl

/-- Add `n` to the first exponent. -/
def shiftFirst (n : ℕ) : TripleExponent ↪ TripleExponent where
  toFun e := ⟨e.first + n, e.second, e.third⟩
  inj' := by
    intro a b h
    apply TripleExponent.ext
    · exact Nat.add_right_cancel
        (congrArg (fun e : TripleExponent => e.first) h)
    · exact congrArg (fun e : TripleExponent => e.second) h
    · exact congrArg (fun e : TripleExponent => e.third) h

/-- Add `n` to the second exponent. -/
def shiftSecond (n : ℕ) : TripleExponent ↪ TripleExponent where
  toFun e := ⟨e.first, e.second + n, e.third⟩
  inj' := by
    intro a b h
    apply TripleExponent.ext
    · exact congrArg (fun e : TripleExponent => e.first) h
    · exact Nat.add_right_cancel
        (congrArg (fun e : TripleExponent => e.second) h)
    · exact congrArg (fun e : TripleExponent => e.third) h

@[simp]
theorem difference_swapFirstSecond (e : TripleExponent) :
    difference (swapFirstSecond e) = -difference e := by
  simp [difference, swapFirstSecond] <;> omega

@[simp]
theorem difference_shiftFirst (n : ℕ) (e : TripleExponent) :
    difference (shiftFirst n e) = (n : ℤ) + difference e := by
  simp [difference, shiftFirst] <;> omega

@[simp]
theorem difference_shiftSecond (n : ℕ) (e : TripleExponent) :
    difference (shiftSecond n e) = difference e - n := by
  simp [difference, shiftSecond] <;> omega

@[simp]
theorem totalDegree_swapFirstSecond (e : TripleExponent) :
    totalDegree (swapFirstSecond e) = totalDegree e := by
  simp [totalDegree, swapFirstSecond] <;> omega

@[simp]
theorem totalDegree_shiftFirst (n : ℕ) (e : TripleExponent) :
    totalDegree (shiftFirst n e) = n + totalDegree e := by
  simp [totalDegree, shiftFirst] <;> omega

@[simp]
theorem totalDegree_shiftSecond (n : ℕ) (e : TripleExponent) :
    totalDegree (shiftSecond n e) = n + totalDegree e := by
  simp [totalDegree, shiftSecond] <;> omega

end TripleExponent

/-- Coefficient block for a polynomial in three tensor variables. -/
abbrev TripleBlock (F : Type*) [Zero F] := TripleExponent →₀ F

/-- Rename the first and second variables of a coefficient block. -/
noncomputable def swapFirstSecondBlock
    {F : Type*} [Zero F] (A : TripleBlock F) : TripleBlock F :=
  A.embDomain TripleExponent.swapFirstSecond.toEmbedding

/-- First summand in the all-distinct transvection output block. -/
noncomputable def positiveShiftTerm
    {F : Type*} [Zero F] (n : ℕ) (A : TripleBlock F) : TripleBlock F :=
  (swapFirstSecondBlock A).embDomain (TripleExponent.shiftFirst n)

/-- Second summand in the all-distinct transvection output block. -/
noncomputable def negativeShiftTerm
    {F : Type*} [Zero F] (n : ℕ) (A : TripleBlock F) : TripleBlock F :=
  A.embDomain (TripleExponent.shiftSecond n)

/-- The first transvection summand has positive exponent difference beyond the support bound. -/
theorem positiveShiftTerm_difference_pos
    {F : Type*} [Zero F]
    (A : TripleBlock F) (n : ℕ)
    (hbound : ∀ e ∈ A.support, |TripleExponent.difference e| < (n : ℤ))
    {x : TripleExponent} (hx : x ∈ (positiveShiftTerm n A).support) :
    0 < TripleExponent.difference x := by
  rw [positiveShiftTerm, Finsupp.support_embDomain] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  rw [swapFirstSecondBlock, Finsupp.support_embDomain] at hy
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hy
  have hb := hbound e he
  have hb_upper : TripleExponent.difference e < (n : ℤ) := (abs_lt.mp hb).2
  simp only [TripleExponent.difference_shiftFirst,
    TripleExponent.difference_swapFirstSecond]
  omega

/-- The second transvection summand has negative exponent difference beyond the support bound. -/
theorem negativeShiftTerm_difference_neg
    {F : Type*} [Zero F]
    (A : TripleBlock F) (n : ℕ)
    (hbound : ∀ e ∈ A.support, |TripleExponent.difference e| < (n : ℤ))
    {x : TripleExponent} (hx : x ∈ (negativeShiftTerm n A).support) :
    TripleExponent.difference x < 0 := by
  rw [negativeShiftTerm, Finsupp.support_embDomain] at hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hx
  have hb := hbound e he
  have hb_upper : TripleExponent.difference e < (n : ℤ) := (abs_lt.mp hb).2
  simpa only [TripleExponent.difference_shiftSecond] using
    (sub_neg.mpr hb_upper)

/-- The two all-distinct transvection summands have disjoint monomial support. -/
theorem positive_negative_shift_support_disjoint
    {F : Type*} [Zero F]
    (A : TripleBlock F) (n : ℕ)
    (hbound : ∀ e ∈ A.support, |TripleExponent.difference e| < (n : ℤ)) :
    Disjoint (positiveShiftTerm n A).support (negativeShiftTerm n A).support := by
  rw [Finset.disjoint_left]
  intro x hxpos hxneg
  have hpos := positiveShiftTerm_difference_pos A n hbound hxpos
  have hneg := negativeShiftTerm_difference_neg A n hbound hxneg
  omega

/-- The first shifted summand is nonzero whenever the source block is nonzero. -/
theorem positiveShiftTerm_ne_zero
    {F : Type*} [Zero F]
    {A : TripleBlock F} (hA : A ≠ 0) (n : ℕ) :
    positiveShiftTerm n A ≠ 0 := by
  simpa [positiveShiftTerm, swapFirstSecondBlock] using hA

/--
The all-distinct transvection output block cannot vanish for shifts beyond the
finite exponent-difference support of a nonzero source block.
-/
theorem allDistinctShiftOutput_ne_zero
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (hA : A ≠ 0) (n : ℕ)
    (hbound : ∀ e ∈ A.support, |TripleExponent.difference e| < (n : ℤ)) :
    positiveShiftTerm n A + negativeShiftTerm n A ≠ 0 :=
  add_ne_zero_of_disjoint_support
    (positiveShiftTerm_ne_zero hA n)
    (positive_negative_shift_support_disjoint A n hbound)

end LeanMathlib.Rigidity
