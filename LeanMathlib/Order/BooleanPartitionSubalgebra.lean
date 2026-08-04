import LeanMathlib.Order.BooleanPartitionCanonical
import Mathlib.Order.BooleanSubalgebra

namespace LeanMathlib

namespace BooleanSubalgebra

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]
variable {L : BooleanSubalgebra α} {a x y z : α}

theorem twoWay_total_mem_of_parts_mem
    (h : TwoWayDecomposition a x y) (hx : x ∈ L) (hy : y ∈ L) :
    a ∈ L := by
  rw [← h.sup_eq]
  exact L.sup_mem hx hy

theorem twoWay_right_mem_of_total_left_mem
    (h : TwoWayDecomposition a x y) (ha : a ∈ L) (hx : x ∈ L) :
    y ∈ L := by
  have hrem : rightSplit a x ∈ L := by
    simpa [rightSplit] using L.sdiff_mem ha hx
  rwa [h.rightSplit_total_left] at hrem

theorem twoWay_left_mem_of_total_right_mem
    (h : TwoWayDecomposition a x y) (ha : a ∈ L) (hy : y ∈ L) :
    x ∈ L := by
  have hrem : rightSplit a y ∈ L := by
    simpa [rightSplit] using L.sdiff_mem ha hy
  rwa [h.rightSplit_total_right] at hrem

theorem threeWay_total_mem_of_parts_mem
    (h : ThreeWayDecomposition a x y z) (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    a ∈ L := by
  rw [← h.sup_eq]
  exact L.sup_mem (L.sup_mem hx hy) hz

theorem threeWay_firstPair_mem_of_first_second_mem
    (_h : ThreeWayDecomposition a x y z) (hx : x ∈ L) (hy : y ∈ L) :
    x ⊔ y ∈ L :=
  L.sup_mem hx hy

theorem threeWay_remainder_mem_of_total_first_mem
    (h : ThreeWayDecomposition a x y z) (ha : a ∈ L) (hx : x ∈ L) :
    y ⊔ z ∈ L := by
  have hrem : rightSplit a x ∈ L := by
    simpa [rightSplit] using L.sdiff_mem ha hx
  rwa [h.rightSplit_total_first] at hrem

theorem threeWay_third_mem_of_total_first_second_mem
    (h : ThreeWayDecomposition a x y z) (ha : a ∈ L) (hx : x ∈ L) (hy : y ∈ L) :
    z ∈ L := by
  have hp : x ⊔ y ∈ L := L.sup_mem hx hy
  have hrem : rightSplit a (x ⊔ y) ∈ L := by
    simpa [rightSplit] using L.sdiff_mem ha hp
  rwa [h.rightSplit_total_firstPair] at hrem

theorem threeWay_second_mem_of_total_first_third_mem
    (h : ThreeWayDecomposition a x y z) (ha : a ∈ L) (hx : x ∈ L) (hz : z ∈ L) :
    y ∈ L := by
  have hyr : y ⊔ z ∈ L := threeWay_remainder_mem_of_total_first_mem h ha hx
  exact twoWay_left_mem_of_total_right_mem
    (a := y ⊔ z) (x := y) (y := z)
    { left_nonzero := h.second_nonzero
      right_nonzero := h.third_nonzero
      disjoint := h.second_third
      sup_eq := rfl }
    hyr hz

end BooleanAlgebra

end BooleanSubalgebra

end LeanMathlib
