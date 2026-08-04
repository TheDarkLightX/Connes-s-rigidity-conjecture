import Mathlib
import LeanMathlib.Rigidity.FinsuppGroupLike

namespace LeanMathlib.Rigidity

open Coalgebra
open scoped TensorProduct

/-- Extract the `(g,h)` coefficient of a tensor of group-algebra vectors. -/
noncomputable def tensorCoefficient
    {G K : Type*} [DecidableEq G] [Field K]
    (g h : G) :
    (MonoidAlgebra K G ⊗[K] MonoidAlgebra K G) →ₗ[K] K :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y => x g * y h
          map_add' := by intro a b; simp [mul_add]
          map_smul' := by intro c y; simp [mul_assoc, mul_left_comm, mul_comm] }
      map_add' := by
        intro a b
        ext y
        simp [add_mul]
      map_smul' := by
        intro c x
        ext y
        simp [mul_assoc] }

@[simp]
theorem tensorCoefficient_tmul
    {G K : Type*} [DecidableEq G] [Field K]
    (g h : G) (x y : MonoidAlgebra K G) :
    tensorCoefficient g h (x ⊗ₜ[K] y) = x g * y h := by
  simp [tensorCoefficient]

/-- The canonical group-algebra counit is the sum of coefficients. -/
theorem groupAlgebra_counit_eq_sum
    {G K : Type*} [DecidableEq G] [Field K]
    (a : MonoidAlgebra K G) :
    Coalgebra.counit (R := K) a = a.sum (fun _ c => c) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g c => simp

/-- The canonical coproduct has only diagonal coefficient support. -/
theorem tensorCoefficient_groupAlgebra_comul
    {G K : Type*} [DecidableEq G] [Field K]
    (a : MonoidAlgebra K G) (g h : G) :
    tensorCoefficient g h (Coalgebra.comul (R := K) a) =
      if g = h then a g else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [tensorCoefficient]
  | add a b ha hb =>
      by_cases hgh : g = h <;> simp [map_add, ha, hb, hgh]
  | single i c =>
      by_cases hgh : g = h <;>
        by_cases hig : i = g <;>
        by_cases hih : i = h <;>
        simp_all [tensorCoefficient]

/--
Mathlib's actual Hopf-algebra predicate on a group algebra is equivalent to
being a canonical basis group element. This closes the semantic bridge from
the coefficient proof to `IsGroupLikeElem`.
-/
theorem isGroupLikeElem_groupAlgebra_iff_single
    {G K : Type*} [DecidableEq G] [Field K]
    (a : MonoidAlgebra K G) :
    IsGroupLikeElem K a ↔ ∃ g, a = Finsupp.single g 1 := by
  constructor
  · intro ha
    apply exact_groupLike_finsupp a
    · rw [← groupAlgebra_counit_eq_sum]
      exact ha.counit_eq_one
    · intro g h
      have hcoeff := congrArg (tensorCoefficient g h) ha.comul_eq_tmul_self
      rw [tensorCoefficient_groupAlgebra_comul] at hcoeff
      simpa [FinsuppGroupLikeEquation] using hcoeff
  · rintro ⟨g, rfl⟩
    constructor <;> simp

/-- The group-like elements of a group algebra are in bijection with the group. -/
noncomputable def groupLikeGroupAlgebraEquiv
    {G K : Type*} [DecidableEq G] [Field K] :
    GroupLike K (MonoidAlgebra K G) ≃ G := by
  let f : G → GroupLike K (MonoidAlgebra K G) := fun g =>
    ⟨Finsupp.single g 1, (isGroupLikeElem_groupAlgebra_iff_single _).2 ⟨g, rfl⟩⟩
  have hf_injective : Function.Injective f := by
    intro g h hEq
    have hval : Finsupp.single g (1 : K) = Finsupp.single h 1 :=
      congrArg GroupLike.val hEq
    by_contra hne
    have hzero : (0 : K) = 1 := by
      simpa [Finsupp.single_apply, hne] using congrFun (DFunLike.congr_fun hval h) h
    exact zero_ne_one hzero
  have hf_surjective : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := (isGroupLikeElem_groupAlgebra_iff_single x.val).1 x.isGroupLikeElem_val
    refine ⟨g, ?_⟩
    apply GroupLike.val_injective
    exact hg.symm
  exact (Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩).symm

end LeanMathlib.Rigidity
