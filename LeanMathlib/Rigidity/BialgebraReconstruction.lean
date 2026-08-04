import Mathlib
import LeanMathlib.Rigidity.GroupAlgebraHopfMulEquiv

namespace LeanMathlib.Rigidity

/-- A bialgebra equivalence restricts to an equivalence of group-like elements. -/
noncomputable def BialgEquiv.groupLikeMulEquiv
    {R A B : Type*}
    [CommSemiring R]
    [Semiring A] [Semiring B]
    [Bialgebra R A] [Bialgebra R B]
    (e : A ≃ₐc[R] B) :
    GroupLike R A ≃* GroupLike R B where
  toFun := fun a => ⟨e a, a.isGroupLikeElem_val.map e⟩
  invFun := fun b => ⟨e.symm b, b.isGroupLikeElem_val.map e.symm⟩
  left_inv := by
    intro a
    apply GroupLike.val_injective
    exact e.symm_apply_apply a
  right_inv := by
    intro b
    apply GroupLike.val_injective
    exact e.apply_symm_apply b
  map_mul' := by
    intro a b
    apply GroupLike.val_injective
    change e (a.1 * b.1) = e a.1 * e b.1
    exact map_mul e a.1 b.1

/--
Any bialgebra equivalence between canonical group algebras reconstructs a group
isomorphism. Therefore an algebra equivalence between nonisomorphic groups must
necessarily fail to preserve the canonical coproduct.
-/
noncomputable def groupMulEquivOfGroupAlgebraBialgEquiv
    {G H K : Type*}
    [DecidableEq G] [DecidableEq H]
    [Group G] [Group H] [Field K]
    (e : MonoidAlgebra K G ≃ₐc[K] MonoidAlgebra K H) :
    G ≃* H :=
  (groupLikeGroupAlgebraMulEquiv (G := G) (K := K)).trans <|
    (BialgEquiv.groupLikeMulEquiv e).trans <|
      (groupLikeGroupAlgebraMulEquiv (G := H) (K := K)).symm

/-- Nonisomorphic groups cannot have bialgebra-equivalent canonical group algebras. -/
theorem no_groupAlgebra_bialgEquiv_of_no_groupEquiv
    {G H K : Type*}
    [DecidableEq G] [DecidableEq H]
    [Group G] [Group H] [Field K]
    (hGH : IsEmpty (G ≃* H)) :
    IsEmpty (MonoidAlgebra K G ≃ₐc[K] MonoidAlgebra K H) :=
  ⟨fun e => hGH.false (groupMulEquivOfGroupAlgebraBialgEquiv e)⟩

end LeanMathlib.Rigidity
