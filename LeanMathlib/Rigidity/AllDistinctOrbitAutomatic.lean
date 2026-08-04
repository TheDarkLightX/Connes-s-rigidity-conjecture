import Mathlib
import LeanMathlib.Rigidity.AllDistinctOrbit

namespace LeanMathlib.Rigidity

/-- Exponent difference is bounded by total monomial degree. -/
theorem abs_difference_le_totalDegree (e : TripleExponent) :
    |TripleExponent.difference e| ≤
      (TripleExponent.totalDegree e : ℤ) := by
  rw [abs_le]
  constructor <;>
    simp [TripleExponent.difference, TripleExponent.totalDegree] <;>
    omega

/--
Every nonzero finite three-variable coefficient block has a maximal total
monomial degree. This packages the upper-bound and witness forms needed by the
orbit theorem.
-/
theorem exists_maximal_totalDegree
    {F : Type*} [Zero F]
    (A : TripleBlock F) (hA : A ≠ 0) :
    ∃ D : ℕ,
      (∀ e ∈ A.support, TripleExponent.totalDegree e ≤ D) ∧
      ∃ e ∈ A.support, TripleExponent.totalDegree e = D := by
  obtain ⟨e₀, he₀⟩ := exists_mem_support_of_ne_zero hA
  let S := {e // e ∈ A.support}
  letI : Nonempty S := ⟨⟨e₀, he₀⟩⟩
  obtain ⟨emax, hmax⟩ :=
    Finite.exists_max (fun e : S => TripleExponent.totalDegree e)
  refine ⟨TripleExponent.totalDegree emax, ?_, ?_⟩
  · intro e he
    exact hmax ⟨e, he⟩
  · exact ⟨emax, emax.property, rfl⟩

/-- One plus a maximal total degree bounds all exponent differences strictly. -/
theorem maximal_totalDegree_bounds_difference
    {F : Type*} [Zero F]
    (A : TripleBlock F) (D : ℕ)
    (hupper : ∀ e ∈ A.support, TripleExponent.totalDegree e ≤ D) :
    ∀ e ∈ A.support,
      |TripleExponent.difference e| < ((D + 1 : ℕ) : ℤ) := by
  intro e he
  have hdiff := abs_difference_le_totalDegree e
  have hdeg := hupper e he
  norm_num at hdiff ⊢
  omega

/--
Unconditional all-distinct block theorem: every nonzero finite block produces
an injective tail of transvection outputs.
-/
theorem exists_allDistinctShiftOutput_tail_injective
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (hA : A ≠ 0) :
    ∃ N : ℕ,
      Function.Injective (fun k : ℕ => allDistinctShiftOutput (N + k) A) := by
  obtain ⟨D, hupper, hwitness⟩ := exists_maximal_totalDegree A hA
  let N := D + 1
  have hbound := maximal_totalDegree_bounds_difference A D hupper
  exact ⟨N,
    allDistinctShiftOutput_tail_injective A N D hbound hupper hwitness⟩

/--
Every nonzero finite block produces infinitely many distinct all-distinct
transvection output blocks. This is the new rank-three replacement for the
fresh-fourth-coordinate step in the rank-four tensor-square proof.
-/
theorem exists_allDistinctShiftOutput_tail_infinite
    {F : Type*} [AddGroup F]
    (A : TripleBlock F) (hA : A ≠ 0) :
    ∃ N : ℕ,
      (Set.range fun k : ℕ => allDistinctShiftOutput (N + k) A).Infinite := by
  obtain ⟨N, hinj⟩ := exists_allDistinctShiftOutput_tail_injective A hA
  exact ⟨N, Set.infinite_range_of_injective hinj⟩

end LeanMathlib.Rigidity
