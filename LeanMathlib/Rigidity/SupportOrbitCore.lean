import Mathlib

namespace LeanMathlib.Rigidity

/-- Every nonzero finitely supported function has a nonzero support point. -/
theorem exists_mem_support_of_ne_zero
    {α R : Type*} [Zero R]
    {f : α →₀ R} (hf : f ≠ 0) :
    ∃ x, x ∈ f.support := by
  by_contra h
  push_neg at h
  apply hf
  ext x
  exact Finsupp.not_mem_support_iff.mp (h x)

/--
Two finitely supported terms with disjoint supports cannot cancel if the first
term is nonzero. This is the algebraic core of the positive/negative
exponent-difference split in the rank-three tensor-cube argument.
-/
theorem add_ne_zero_of_disjoint_support
    {α R : Type*} [AddGroup R]
    {f g : α →₀ R}
    (hf : f ≠ 0)
    (hdisjoint : Disjoint f.support g.support) :
    f + g ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_mem_support_of_ne_zero hf
  have hx_not_g : x ∉ g.support := by
    intro hxg
    exact Finset.disjoint_left.mp hdisjoint hx hxg
  have hfx : f x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hgx : g x = 0 := Finsupp.not_mem_support_iff.mp hx_not_g
  intro hsum
  have hpoint := DFunLike.congr_fun hsum x
  simp [hgx] at hpoint
  exact hfx hpoint

/--
If every nonzero coefficient of `orbitTerm n` lies in total degree `n + d`,
then the family is injective. This turns support separation into an infinite
orbit certificate without comparing full tensors.
-/
theorem injective_of_support_degree
    {α R : Type*} [Zero R]
    (orbitTerm : ℕ → α →₀ R)
    (degree : α → ℕ) (d : ℕ)
    (hnonzero : ∀ n, orbitTerm n ≠ 0)
    (hdegree : ∀ n x, x ∈ (orbitTerm n).support → degree x = n + d) :
    Function.Injective orbitTerm := by
  intro m n hmn
  obtain ⟨x, hx⟩ := exists_mem_support_of_ne_zero (hnonzero m)
  have hxm : degree x = m + d := hdegree m x hx
  have hxn_mem : x ∈ (orbitTerm n).support := by
    rw [← hmn]
    exact hx
  have hxn : degree x = n + d := hdegree n x hxn_mem
  omega

/-- An injective support-homogeneous family has infinite range. -/
theorem infinite_range_of_support_degree
    {α R : Type*} [Zero R]
    (orbitTerm : ℕ → α →₀ R)
    (degree : α → ℕ) (d : ℕ)
    (hnonzero : ∀ n, orbitTerm n ≠ 0)
    (hdegree : ∀ n x, x ∈ (orbitTerm n).support → degree x = n + d) :
    (Set.range orbitTerm).Infinite :=
  Set.infinite_range_of_injective
    (injective_of_support_degree orbitTerm degree d hnonzero hdegree)

end LeanMathlib.Rigidity
