import LeanMathlib.Order.BooleanPartitionTransport
import LeanMathlib.Order.BooleanWeakPartition

namespace LeanMathlib

namespace BoundedLatticeHom

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem map_weakTwoWayDecomposition (f : BoundedLatticeHom α β) {a x y : α}
    (h : WeakTwoWayDecomposition a x y) :
    WeakTwoWayDecomposition (f a) (f x) (f y) where
  disjoint := map_disjoint f h.disjoint
  sup_eq := by
    calc
      f x ⊔ f y = f (x ⊔ y) := by simp
      _ = f a := by rw [h.sup_eq]

theorem map_weakThreeWayDecomposition (f : BoundedLatticeHom α β) {a x y z : α}
    (h : WeakThreeWayDecomposition a x y z) :
    WeakThreeWayDecomposition (f a) (f x) (f y) (f z) where
  first_second := map_disjoint f h.first_second
  first_third := map_disjoint f h.first_third
  second_third := map_disjoint f h.second_third
  sup_eq := by
    calc
      (f x ⊔ f y) ⊔ f z = f ((x ⊔ y) ⊔ z) := by simp
      _ = f a := by rw [h.sup_eq]

theorem map_weakFourWayDecomposition (f : BoundedLatticeHom α β) {a w x y z : α}
    (h : WeakFourWayDecomposition a w x y z) :
    WeakFourWayDecomposition (f a) (f w) (f x) (f y) (f z) where
  first_second := map_disjoint f h.first_second
  first_third := map_disjoint f h.first_third
  first_fourth := map_disjoint f h.first_fourth
  second_third := map_disjoint f h.second_third
  second_fourth := map_disjoint f h.second_fourth
  third_fourth := map_disjoint f h.third_fourth
  sup_eq := by
    calc
      ((f w ⊔ f x) ⊔ f y) ⊔ f z = f (((w ⊔ x) ⊔ y) ⊔ z) := by simp
      _ = f a := by rw [h.sup_eq]

end BooleanAlgebra

end BoundedLatticeHom

namespace OrderIso

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem map_weakTwoWayDecomposition (e : α ≃o β) {a x y : α}
    (h : WeakTwoWayDecomposition a x y) :
    WeakTwoWayDecomposition (e a) (e x) (e y) :=
  BoundedLatticeHom.map_weakTwoWayDecomposition (e : BoundedLatticeHom α β) h

theorem map_weakThreeWayDecomposition (e : α ≃o β) {a x y z : α}
    (h : WeakThreeWayDecomposition a x y z) :
    WeakThreeWayDecomposition (e a) (e x) (e y) (e z) :=
  BoundedLatticeHom.map_weakThreeWayDecomposition (e : BoundedLatticeHom α β) h

theorem map_weakFourWayDecomposition (e : α ≃o β) {a w x y z : α}
    (h : WeakFourWayDecomposition a w x y z) :
    WeakFourWayDecomposition (e a) (e w) (e x) (e y) (e z) :=
  BoundedLatticeHom.map_weakFourWayDecomposition (e : BoundedLatticeHom α β) h

theorem weakTwoWayDecomposition_iff (e : α ≃o β) {a x y : α} :
    WeakTwoWayDecomposition (e a) (e x) (e y) ↔ WeakTwoWayDecomposition a x y := by
  constructor
  · intro h
    have hp :=
      map_weakTwoWayDecomposition e.symm (a := e a) (x := e x) (y := e y) h
    simpa using hp
  · exact map_weakTwoWayDecomposition e

theorem weakThreeWayDecomposition_iff (e : α ≃o β) {a x y z : α} :
    WeakThreeWayDecomposition (e a) (e x) (e y) (e z) ↔
      WeakThreeWayDecomposition a x y z := by
  constructor
  · intro h
    have hp :=
      map_weakThreeWayDecomposition e.symm
        (a := e a) (x := e x) (y := e y) (z := e z) h
    simpa using hp
  · exact map_weakThreeWayDecomposition e

theorem weakFourWayDecomposition_iff (e : α ≃o β) {a w x y z : α} :
    WeakFourWayDecomposition (e a) (e w) (e x) (e y) (e z) ↔
      WeakFourWayDecomposition a w x y z := by
  constructor
  · intro h
    have hp :=
      map_weakFourWayDecomposition e.symm
        (a := e a) (w := e w) (x := e x) (y := e y) (z := e z) h
    simpa using hp
  · exact map_weakFourWayDecomposition e

end BooleanAlgebra

end OrderIso

end LeanMathlib
