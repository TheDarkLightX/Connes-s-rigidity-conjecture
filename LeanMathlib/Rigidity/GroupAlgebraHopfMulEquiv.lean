import Mathlib
import LeanMathlib.Rigidity.GroupAlgebraHopfBridge

namespace LeanMathlib.Rigidity

/-- The canonical embedding of a group into the group-like elements of its group algebra. -/
noncomputable def groupToGroupLikeHom
    {G K : Type*} [DecidableEq G] [Field K] :
    G →* GroupLike K (MonoidAlgebra K G) where
  toFun := fun g =>
    ⟨Finsupp.single g 1,
      (isGroupLikeElem_groupAlgebra_iff_single _).2 ⟨g, rfl⟩⟩
  map_one' := by
    apply GroupLike.val_injective
    simp
  map_mul' := by
    intro g h
    apply GroupLike.val_injective
    simp

/-- The canonical group-to-group-like homomorphism is injective. -/
theorem groupToGroupLikeHom_injective
    {G K : Type*} [DecidableEq G] [Field K] :
    Function.Injective (groupToGroupLikeHom (G := G) (K := K)) := by
  intro g h hEq
  have hval : Finsupp.single g (1 : K) = Finsupp.single h 1 :=
    congrArg GroupLike.val hEq
  by_contra hne
  have hcoeff := DFunLike.congr_fun hval g
  have hgh : h ≠ g := by exact fun hEq' => hne hEq'.symm
  simp [Finsupp.single_apply, hne, hgh] at hcoeff

/-- The canonical group-to-group-like homomorphism is surjective. -/
theorem groupToGroupLikeHom_surjective
    {G K : Type*} [DecidableEq G] [Field K] :
    Function.Surjective (groupToGroupLikeHom (G := G) (K := K)) := by
  intro x
  obtain ⟨g, hg⟩ :=
    (isGroupLikeElem_groupAlgebra_iff_single x.val).1 x.isGroupLikeElem_val
  refine ⟨g, ?_⟩
  apply GroupLike.val_injective
  exact hg.symm

/--
The group-like elements of the canonical Hopf algebra `K[G]` recover `G` as
a group, not merely as a set. This is the exact algebraic reconstruction result
needed for distinguishing the incompatible Hopf structures in the rigidity
counterexample.
-/
noncomputable def groupLikeGroupAlgebraMulEquiv
    {G K : Type*} [DecidableEq G] [Field K] :
    G ≃* GroupLike K (MonoidAlgebra K G) :=
  MulEquiv.ofBijective (groupToGroupLikeHom (G := G) (K := K))
    ⟨groupToGroupLikeHom_injective, groupToGroupLikeHom_surjective⟩

end LeanMathlib.Rigidity
