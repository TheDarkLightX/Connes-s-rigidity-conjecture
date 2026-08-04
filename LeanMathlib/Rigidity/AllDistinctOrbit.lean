import Mathlib
import LeanMathlib.Rigidity.TripleExponentBlock
import LeanMathlib.Rigidity.SupportMaxDegree

namespace LeanMathlib.Rigidity

/-- The repeated-coordinate output block created from an all-distinct source block. -/
def allDistinctShiftOutput
    {F : Type*} [AddGroup F] (n : ℕ) (A : TripleBlock F) : TripleBlock F :=
  positiveShiftTerm n A + negativeShiftTerm n A

/-- A positive shifted monomial has total degree increased by `n`. -/
theorem positiveShiftTerm_totalDegree
    {F : Type*} [Zero F]
    (A : TripleBlock F) (n : ℕ)
    {x : TripleExponent} (hx : x ∈ (positiveShiftTerm n A).support) :
    ∃ e ∈ A.support,
      TripleExponent.totalDegree x = n + TripleExponent.totalDegree e := by
  rw [positiveShiftTerm, Finsupp.support_embDomain] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  rw [swapFirstSecondBlock, Finsupp.support_embDomain] at hy
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hy
  exact ⟨e, he, by simp⟩

/-- A negative shifted monomial has total degree increased by `n`. -/
theorem negativeShiftTerm_totalDegree
    {F : Type*} [Zero F]
    (A : TripleBlock F) (n : ℕ)
    {x : TripleExponent} (hx : x ∈ (negativeShiftTerm n A).support) :
    ∃ e ∈ A.support,
      TripleExponent.totalDegree x = n + TripleExponent.totalDegree e := by
  rw [negativeShiftTerm, Finsupp.support_embDomain] at hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hx
  exact ⟨e, he, by simp⟩

/-- A source support degree bound shifts by exactly `n` in the output block. -/
theorem allDistinctShiftOutput_degree_upper
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (D n : ℕ)
    (hupperA : ∀ e ∈ A.support, TripleExponent.totalDegree e ≤ D)
    {x : TripleExponent} (hx : x ∈ (allDistinctShiftOutput n A).support) :
    TripleExponent.totalDegree x ≤ n + D := by
  have hxside := mem_support_left_or_right_of_mem_add hx
  rcases hxside with hxpos | hxneg
  · obtain ⟨e, he, hdeg⟩ := positiveShiftTerm_totalDegree A n hxpos
    rw [hdeg]
    exact Nat.add_le_add_left (hupperA e he) n
  · obtain ⟨e, he, hdeg⟩ := negativeShiftTerm_totalDegree A n hxneg
    rw [hdeg]
    exact Nat.add_le_add_left (hupperA e he) n

/-- A maximal-degree source monomial survives in the output under support separation. -/
theorem allDistinctShiftOutput_degree_witness
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (D n : ℕ)
    (hbound : ∀ e ∈ A.support, |TripleExponent.difference e| < (n : ℤ))
    (hwitnessA : ∃ e ∈ A.support, TripleExponent.totalDegree e = D) :
    ∃ x ∈ (allDistinctShiftOutput n A).support,
      TripleExponent.totalDegree x = n + D := by
  obtain ⟨e, he, hdeg⟩ := hwitnessA
  let y := TripleExponent.swapFirstSecond e
  let x := TripleExponent.shiftFirst n y
  have hy : y ∈ (swapFirstSecondBlock A).support := by
    rw [swapFirstSecondBlock, Finsupp.support_embDomain]
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  have hxpos : x ∈ (positiveShiftTerm n A).support := by
    rw [positiveShiftTerm, Finsupp.support_embDomain]
    exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
  have hdisjoint := positive_negative_shift_support_disjoint A n hbound
  have hxout : x ∈ (allDistinctShiftOutput n A).support := by
    exact mem_support_add_of_disjoint hxpos hdisjoint
  refine ⟨x, hxout, ?_⟩
  simp [x, y, hdeg]

/--
For every nonzero finite block, choose a shift threshold larger than every
first/second exponent difference. Beyond that threshold, the all-distinct
transvection outputs form an injective family, provided `D` is the maximal
source total degree.
-/
theorem allDistinctShiftOutput_tail_injective
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (N D : ℕ)
    (hboundN : ∀ e ∈ A.support, |TripleExponent.difference e| < (N : ℤ))
    (hupperA : ∀ e ∈ A.support, TripleExponent.totalDegree e ≤ D)
    (hwitnessA : ∃ e ∈ A.support, TripleExponent.totalDegree e = D) :
    Function.Injective (fun k : ℕ => allDistinctShiftOutput (N + k) A) := by
  apply injective_of_moving_max_support_degree
    (fun k : ℕ => allDistinctShiftOutput (N + k) A)
    TripleExponent.totalDegree (N + D)
  · intro k x hx
    have h := allDistinctShiftOutput_degree_upper A D (N + k) hupperA hx
    omega
  · intro k
    have hboundk :
        ∀ e ∈ A.support,
          |TripleExponent.difference e| < ((N + k : ℕ) : ℤ) := by
      intro e he
      have hbase := hboundN e he
      norm_num at hbase ⊢
      omega
    obtain ⟨x, hx, hdeg⟩ :=
      allDistinctShiftOutput_degree_witness A D (N + k) hboundk hwitnessA
    refine ⟨x, hx, ?_⟩
    omega

/-- The all-distinct transvection output has infinite range beyond the support threshold. -/
theorem allDistinctShiftOutput_tail_infinite
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (N D : ℕ)
    (hboundN : ∀ e ∈ A.support, |TripleExponent.difference e| < (N : ℤ))
    (hupperA : ∀ e ∈ A.support, TripleExponent.totalDegree e ≤ D)
    (hwitnessA : ∃ e ∈ A.support, TripleExponent.totalDegree e = D) :
    (Set.range fun k : ℕ => allDistinctShiftOutput (N + k) A).Infinite :=
  Set.infinite_range_of_injective
    (allDistinctShiftOutput_tail_injective A N D hboundN hupperA hwitnessA)

end LeanMathlib.Rigidity
