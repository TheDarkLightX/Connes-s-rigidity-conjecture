import Mathlib
import LeanMathlib.Rigidity.AllDistinctOrbitAutomatic

namespace LeanMathlib.Rigidity

/-- Shift a three-variable coefficient block in its first exponent. -/
def singleShiftTerm
    {F : Type*} [Zero F] (n : ℕ) (A : TripleBlock F) : TripleBlock F :=
  A.embDomain (TripleExponent.shiftFirst n)

/-- A shifted support monomial has total degree increased by the shift. -/
theorem singleShiftTerm_totalDegree
    {F : Type*} [Zero F]
    (A : TripleBlock F) (n : ℕ)
    {x : TripleExponent} (hx : x ∈ (singleShiftTerm n A).support) :
    ∃ e ∈ A.support,
      TripleExponent.totalDegree x = n + TripleExponent.totalDegree e := by
  rw [singleShiftTerm, Finsupp.support_embDomain] at hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hx
  exact ⟨e, he, by simp⟩

/-- A source degree bound shifts by exactly `n`. -/
theorem singleShiftTerm_degree_upper
    {F : Type*} [Zero F]
    (A : TripleBlock F) (D n : ℕ)
    (hupperA : ∀ e ∈ A.support, TripleExponent.totalDegree e ≤ D)
    {x : TripleExponent} (hx : x ∈ (singleShiftTerm n A).support) :
    TripleExponent.totalDegree x ≤ n + D := by
  obtain ⟨e, he, hdeg⟩ := singleShiftTerm_totalDegree A n hx
  rw [hdeg]
  exact Nat.add_le_add_left (hupperA e he) n

/-- A maximal-degree source monomial survives every single shift. -/
theorem singleShiftTerm_degree_witness
    {F : Type*} [Zero F]
    (A : TripleBlock F) (D n : ℕ)
    (hwitnessA : ∃ e ∈ A.support, TripleExponent.totalDegree e = D) :
    ∃ x ∈ (singleShiftTerm n A).support,
      TripleExponent.totalDegree x = n + D := by
  obtain ⟨e, he, hdeg⟩ := hwitnessA
  refine ⟨TripleExponent.shiftFirst n e, ?_, ?_⟩
  · rw [singleShiftTerm, Finsupp.support_embDomain]
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  · simp [hdeg]

/-- Every nonzero finite block has an injective single-shift orbit family. -/
theorem singleShiftTerm_injective
    {F : Type*} [Zero F]
    (A : TripleBlock F) (hA : A ≠ 0) :
    Function.Injective (fun n : ℕ => singleShiftTerm n A) := by
  obtain ⟨D, hupper, hwitness⟩ := exists_maximal_totalDegree A hA
  apply injective_of_moving_max_support_degree
    (fun n : ℕ => singleShiftTerm n A)
    TripleExponent.totalDegree D
  · intro n x hx
    exact singleShiftTerm_degree_upper A D n hupper hx
  · intro n
    exact singleShiftTerm_degree_witness A D n hwitness

/-- Every nonzero finite block has an infinite single-shift orbit family. -/
theorem singleShiftTerm_infinite
    {F : Type*} [Zero F]
    (A : TripleBlock F) (hA : A ≠ 0) :
    (Set.range fun n : ℕ => singleShiftTerm n A).Infinite :=
  Set.infinite_range_of_injective (singleShiftTerm_injective A hA)

end LeanMathlib.Rigidity
