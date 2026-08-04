import Mathlib
import LeanMathlib.Rigidity.SupportOrbitCore

namespace LeanMathlib.Rigidity

/-- A support point survives addition when the other summand has disjoint support. -/
theorem mem_support_add_of_disjoint
    {α R : Type*} [AddGroup R]
    {f g : α →₀ R} {x : α}
    (hx : x ∈ f.support)
    (hdisjoint : Disjoint f.support g.support) :
    x ∈ (f + g).support := by
  have hx_not_g : x ∉ g.support := by
    intro hxg
    exact Finset.disjoint_left.mp hdisjoint hx hxg
  have hfx : f x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hgx : g x = 0 := Finsupp.notMem_support_iff.mp hx_not_g
  apply Finsupp.mem_support_iff.mpr
  simp [hgx, hfx]

/-- Every support point of a sum comes from at least one summand support. -/
theorem mem_support_left_or_right_of_mem_add
    {α R : Type*} [AddGroup R]
    {f g : α →₀ R} {x : α}
    (hx : x ∈ (f + g).support) :
    x ∈ f.support ∨ x ∈ g.support := by
  by_contra h
  push Not at h
  have hfx : f x = 0 := Finsupp.notMem_support_iff.mp h.1
  have hgx : g x = 0 := Finsupp.notMem_support_iff.mp h.2
  exact Finsupp.mem_support_iff.mp hx (by simp [hfx, hgx])

/--
If the maximal support degree of `orbitTerm n` is exactly `n + D`, then the
family is injective. The theorem is phrased using upper bounds and witnesses,
so it does not depend on a particular maximum-degree API.
-/
theorem injective_of_moving_max_support_degree
    {α R : Type*} [Zero R]
    (orbitTerm : ℕ → α →₀ R)
    (degree : α → ℕ) (D : ℕ)
    (hupper : ∀ n x, x ∈ (orbitTerm n).support → degree x ≤ n + D)
    (hwitness : ∀ n, ∃ x ∈ (orbitTerm n).support, degree x = n + D) :
    Function.Injective orbitTerm := by
  intro m n hmn
  obtain ⟨xm, hxm, hdegm⟩ := hwitness m
  obtain ⟨xn, hxn, hdegn⟩ := hwitness n
  have hxm_n : xm ∈ (orbitTerm n).support := by
    rw [← hmn]
    exact hxm
  have hxn_m : xn ∈ (orbitTerm m).support := by
    rw [hmn]
    exact hxn
  have hmn_le : m + D ≤ n + D := by
    rw [← hdegm]
    exact hupper n xm hxm_n
  have hnm_le : n + D ≤ m + D := by
    rw [← hdegn]
    exact hupper m xn hxn_m
  omega

/-- A family with moving maximal support degree has infinite range. -/
theorem infinite_range_of_moving_max_support_degree
    {α R : Type*} [Zero R]
    (orbitTerm : ℕ → α →₀ R)
    (degree : α → ℕ) (D : ℕ)
    (hupper : ∀ n x, x ∈ (orbitTerm n).support → degree x ≤ n + D)
    (hwitness : ∀ n, ∃ x ∈ (orbitTerm n).support, degree x = n + D) :
    (Set.range orbitTerm).Infinite :=
  Set.infinite_range_of_injective
    (injective_of_moving_max_support_degree orbitTerm degree D hupper hwitness)

end LeanMathlib.Rigidity
