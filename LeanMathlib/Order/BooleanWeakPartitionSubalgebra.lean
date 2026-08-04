import LeanMathlib.Order.BooleanWeakPartition
import Mathlib.Order.BooleanSubalgebra

namespace LeanMathlib

namespace BooleanSubalgebra

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]
variable {L : BooleanSubalgebra α} {a w x y z u v : α}

theorem weakTwoWay_total_mem_of_parts_mem
    (h : WeakTwoWayDecomposition a x y) (hx : x ∈ L) (hy : y ∈ L) :
    a ∈ L := by
  rw [← h.sup_eq]
  exact L.sup_mem hx hy

theorem weakTwoWay_right_mem_of_total_left_mem
    (h : WeakTwoWayDecomposition a x y) (ha : a ∈ L) (hx : x ∈ L) :
    y ∈ L := by
  have hrem : rightSplit a x ∈ L := by
    simpa [rightSplit] using L.sdiff_mem ha hx
  rwa [h.rightSplit_total_left] at hrem

theorem weakTwoWay_left_mem_of_total_right_mem
    (h : WeakTwoWayDecomposition a x y) (ha : a ∈ L) (hy : y ∈ L) :
    x ∈ L := by
  have hrem : rightSplit a y ∈ L := by
    simpa [rightSplit] using L.sdiff_mem ha hy
  rwa [h.rightSplit_total_right] at hrem

theorem weakThreeWay_total_mem_of_parts_mem
    (h : WeakThreeWayDecomposition a x y z)
    (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    a ∈ L := by
  rw [← h.sup_eq]
  exact L.sup_mem (L.sup_mem hx hy) hz

theorem weakThreeWay_firstPair_mem_of_first_second_mem
    (_h : WeakThreeWayDecomposition a x y z) (hx : x ∈ L) (hy : y ∈ L) :
    x ⊔ y ∈ L :=
  L.sup_mem hx hy

theorem weakThreeWay_remainder_mem_of_total_first_mem
    (h : WeakThreeWayDecomposition a x y z) (ha : a ∈ L) (hx : x ∈ L) :
    y ⊔ z ∈ L :=
  weakTwoWay_right_mem_of_total_left_mem h.toWeakTwoWayRight ha hx

theorem weakThreeWay_third_mem_of_total_first_second_mem
    (h : WeakThreeWayDecomposition a x y z) (ha : a ∈ L) (hx : x ∈ L) (hy : y ∈ L) :
    z ∈ L := by
  have hp : x ⊔ y ∈ L := L.sup_mem hx hy
  exact weakTwoWay_right_mem_of_total_left_mem h.toWeakTwoWayLeft ha hp

theorem weakThreeWay_second_mem_of_total_first_third_mem
    (h : WeakThreeWayDecomposition a x y z) (ha : a ∈ L) (hx : x ∈ L) (hz : z ∈ L) :
    y ∈ L := by
  have hyr : y ⊔ z ∈ L := weakThreeWay_remainder_mem_of_total_first_mem h ha hx
  exact weakTwoWay_left_mem_of_total_right_mem
    (a := y ⊔ z) (x := y) (y := z)
    { disjoint := h.second_third
      sup_eq := rfl }
    hyr hz

theorem weakFourWay_total_mem_of_parts_mem
    (h : WeakFourWayDecomposition a w x y z)
    (hw : w ∈ L) (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    a ∈ L := by
  rw [← h.sup_eq]
  exact L.sup_mem (L.sup_mem (L.sup_mem hw hx) hy) hz

theorem weakFourWay_firstPair_mem_of_first_second_mem
    (_h : WeakFourWayDecomposition a w x y z) (hw : w ∈ L) (hx : x ∈ L) :
    w ⊔ x ∈ L :=
  L.sup_mem hw hx

theorem weakFourWay_firstTriple_mem_of_first_second_third_mem
    (_h : WeakFourWayDecomposition a w x y z) (hw : w ∈ L) (hx : x ∈ L) (hy : y ∈ L) :
    (w ⊔ x) ⊔ y ∈ L :=
  L.sup_mem (L.sup_mem hw hx) hy

theorem weakFourWay_fourth_mem_of_total_first_second_third_mem
    (h : WeakFourWayDecomposition a w x y z) (ha : a ∈ L)
    (hw : w ∈ L) (hx : x ∈ L) (hy : y ∈ L) :
    z ∈ L := by
  have htriple : (w ⊔ x) ⊔ y ∈ L :=
    weakFourWay_firstTriple_mem_of_first_second_third_mem h hw hx hy
  exact weakTwoWay_right_mem_of_total_left_mem h.toWeakTwoWayLeft ha htriple

theorem weakCommonRefinement_cells_mem
    (_h₁ : WeakTwoWayDecomposition a x y) (_h₂ : WeakTwoWayDecomposition a u v)
    (hx : x ∈ L) (hy : y ∈ L) (hu : u ∈ L) (hv : v ∈ L) :
    (x ⊓ u ∈ L) ∧ (x ⊓ v ∈ L) ∧ (y ⊓ u ∈ L) ∧ (y ⊓ v ∈ L) :=
  ⟨L.inf_mem hx hu, L.inf_mem hx hv, L.inf_mem hy hu, L.inf_mem hy hv⟩

theorem weakCommonRefinement_total_mem_of_parts_mem
    (h₁ : WeakTwoWayDecomposition a x y) (h₂ : WeakTwoWayDecomposition a u v)
    (hx : x ∈ L) (hy : y ∈ L) (hu : u ∈ L) (hv : v ∈ L) :
    a ∈ L := by
  rcases weakCommonRefinement_cells_mem (L := L) h₁ h₂ hx hy hu hv with
    ⟨hxu, hxv, hyu, hyv⟩
  exact weakFourWay_total_mem_of_parts_mem
    (WeakFourWayDecomposition.commonRefinement h₁ h₂) hxu hxv hyu hyv

end BooleanAlgebra

end BooleanSubalgebra

end LeanMathlib
