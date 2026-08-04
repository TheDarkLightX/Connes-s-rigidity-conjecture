import LeanMathlib.Order.BooleanFourWayPartition
import LeanMathlib.Order.BooleanWeakPartitionSubalgebra
import Mathlib.Order.BooleanSubalgebra

namespace LeanMathlib

namespace BooleanSubalgebra

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]
variable {L : BooleanSubalgebra α} {a w x y z : α}

theorem fourWay_total_mem_of_parts_mem
    (h : FourWayDecomposition a w x y z)
    (hw : w ∈ L) (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    a ∈ L :=
  weakFourWay_total_mem_of_parts_mem h.toWeak hw hx hy hz

theorem fourWay_firstPair_mem_of_first_second_mem
    (_h : FourWayDecomposition a w x y z) (hw : w ∈ L) (hx : x ∈ L) :
    w ⊔ x ∈ L :=
  L.sup_mem hw hx

theorem fourWay_firstTriple_mem_of_first_second_third_mem
    (_h : FourWayDecomposition a w x y z) (hw : w ∈ L) (hx : x ∈ L) (hy : y ∈ L) :
    (w ⊔ x) ⊔ y ∈ L :=
  L.sup_mem (L.sup_mem hw hx) hy

theorem fourWay_fourth_mem_of_total_first_second_third_mem
    (h : FourWayDecomposition a w x y z) (ha : a ∈ L)
    (hw : w ∈ L) (hx : x ∈ L) (hy : y ∈ L) :
    z ∈ L :=
  weakFourWay_fourth_mem_of_total_first_second_third_mem h.toWeak ha hw hx hy

theorem fourWay_thirdFourth_mem_of_total_first_second_mem
    (h : FourWayDecomposition a w x y z) (ha : a ∈ L) (hw : w ∈ L) (hx : x ∈ L) :
    y ⊔ z ∈ L := by
  have hpair : w ⊔ x ∈ L := L.sup_mem hw hx
  exact weakTwoWay_right_mem_of_total_left_mem h.toWeak.toWeakTwoWayPairPair ha hpair

theorem fourWay_third_mem_of_total_first_second_fourth_mem
    (h : FourWayDecomposition a w x y z) (ha : a ∈ L)
    (hw : w ∈ L) (hx : x ∈ L) (hz : z ∈ L) :
    y ∈ L := by
  have hyz : y ⊔ z ∈ L := fourWay_thirdFourth_mem_of_total_first_second_mem h ha hw hx
  exact weakTwoWay_left_mem_of_total_right_mem
    (a := y ⊔ z) (x := y) (y := z)
    { disjoint := h.third_fourth
      sup_eq := rfl }
    hyz hz

theorem fourWay_second_mem_of_total_first_third_fourth_mem
    (h : FourWayDecomposition a w x y z) (ha : a ∈ L)
    (hw : w ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    x ∈ L := by
  have hrest : (x ⊔ y) ⊔ z ∈ L :=
    weakTwoWay_right_mem_of_total_left_mem h.toWeak.toWeakTwoWayFirstRest ha hw
  have hxy : x ⊔ y ∈ L :=
    weakTwoWay_left_mem_of_total_right_mem
      (a := (x ⊔ y) ⊔ z) (x := x ⊔ y) (y := z)
      { disjoint := h.second_fourth.sup_left h.third_fourth
        sup_eq := rfl }
      hrest hz
  exact weakTwoWay_left_mem_of_total_right_mem
    (a := x ⊔ y) (x := x) (y := y)
    { disjoint := h.second_third
      sup_eq := rfl }
    hxy hy

theorem fourWay_first_mem_of_total_second_third_fourth_mem
    (h : FourWayDecomposition a w x y z) (ha : a ∈ L)
    (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    w ∈ L := by
  have htriple : (w ⊔ x) ⊔ y ∈ L :=
    weakTwoWay_left_mem_of_total_right_mem h.toWeak.toWeakTwoWayLeft ha hz
  have hwx : w ⊔ x ∈ L :=
    weakTwoWay_left_mem_of_total_right_mem
      (a := (w ⊔ x) ⊔ y) (x := w ⊔ x) (y := y)
      { disjoint := h.first_third.sup_left h.second_third
        sup_eq := rfl }
      htriple hy
  exact weakTwoWay_left_mem_of_total_right_mem
    (a := w ⊔ x) (x := w) (y := x)
    { disjoint := h.first_second
      sup_eq := rfl }
    hwx hx

end BooleanAlgebra

end BooleanSubalgebra

end LeanMathlib
