import Mathlib
import LeanMathlib.Rigidity.CubeCoordinateTransvection

namespace LeanMathlib.Rigidity

/-- A nonzero cube-coordinate tensor has a nonzero coordinate block. -/
theorem exists_nonzero_cubeCoordinateBlock
    {F : Type*} [Zero F]
    {w : CubeCoordinateBlock F} (hw : w ≠ 0) :
    ∃ a b c, w a b c ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  funext a b c
  exact h a b c

/-- Three repeated labels in `Fin 3` leave a fresh coordinate. -/
theorem exists_fresh_coordinate_of_repeated
    (a b c : Fin 3)
    (hrepeated : a = b ∨ a = c ∨ b = c) :
    ∃ i : Fin 3, i ≠ a ∧ i ≠ b ∧ i ≠ c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

/-- If no repeated-label block is nonzero, all repeated-label blocks vanish. -/
theorem repeatedBlocksZero_of_no_nonzero_repeated
    {F : Type*} [Zero F]
    (w : CubeCoordinateBlock F)
    (h : ¬ ∃ a b c,
      (a = b ∨ a = c ∨ b = c) ∧ w a b c ≠ 0) :
    RepeatedCoordinateBlocksZero w := by
  intro a b c hrepeated
  by_contra hne
  exact h ⟨a, b, c, hrepeated, hne⟩

/--
Global coordinate-level rank-three theorem.

Every nonzero cube-coordinate tensor symmetric in its first two slots admits
an elementary transvection and an observed coordinate block whose shifted tail
has infinite range. The proof splits into:

* a nonzero repeated-label block, handled by a fresh coordinate and a single
  shifted term;
* no nonzero repeated-label blocks, where a nonzero all-distinct block is
  handled by the separated two-term argument.
-/
theorem symmetricCubeCoordinate_has_infinite_transvection_observation
    {F : Type*} [AddGroup F]
    (w : CubeCoordinateBlock F)
    (hw : w ≠ 0)
    (hsym : SwapFirstTwoSymmetric w) :
    ∃ (target source out₁ out₂ out₃ : Fin 3) (N : ℕ),
      target ≠ source ∧ target ≠ out₃ ∧
      (Set.range fun n : ℕ =>
        firstTwoTransvectionOutput target source (N + n)
          w out₁ out₂ out₃).Infinite := by
  by_cases hrepeated : ∃ a b c,
      (a = b ∨ a = c ∨ b = c) ∧ w a b c ≠ 0
  · obtain ⟨source, b, c, hrep, hsource⟩ := hrepeated
    obtain ⟨target, htarget_source, htarget_b, htarget_c⟩ :=
      exists_fresh_coordinate_of_repeated source b c hrep
    refine ⟨target, source, target, b, c, 0,
      htarget_source, htarget_c, ?_⟩
    have hinfinite :=
      freshCoordinate_output_infinite w target source b c
        htarget_b htarget_c hsource
    simpa using hinfinite
  · have hzero : RepeatedCoordinateBlocksZero w :=
      repeatedBlocksZero_of_no_nonzero_repeated w hrepeated
    obtain ⟨i, j, k, hsource⟩ := exists_nonzero_cubeCoordinateBlock hw
    have hij : i ≠ j := by
      intro hEq
      apply hsource
      exact hzero i j k (Or.inl hEq)
    have hik : i ≠ k := by
      intro hEq
      apply hsource
      exact hzero i j k (Or.inr (Or.inl hEq))
    obtain ⟨N, hinfinite⟩ :=
      allDistinct_output_tail_infinite w hzero hsym i j k hsource
    exact ⟨i, j, i, i, k, N, hij, hik, hinfinite⟩

end LeanMathlib.Rigidity
