import LeanMathlib.Order.BooleanFourWayPartition
import LeanMathlib.Order.BooleanPartitionTransport

namespace LeanMathlib

namespace BoundedLatticeHom

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem map_fourWayDecomposition (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) {a w x y z : α}
    (h : FourWayDecomposition a w x y z) :
    FourWayDecomposition (f a) (f w) (f x) (f y) (f z) where
  first_nonzero := map_ne_bot_of_injective f hf h.first_nonzero
  second_nonzero := map_ne_bot_of_injective f hf h.second_nonzero
  third_nonzero := map_ne_bot_of_injective f hf h.third_nonzero
  fourth_nonzero := map_ne_bot_of_injective f hf h.fourth_nonzero
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

theorem map_fourWayDecomposition (e : α ≃o β) {a w x y z : α}
    (h : FourWayDecomposition a w x y z) :
    FourWayDecomposition (e a) (e w) (e x) (e y) (e z) :=
  BoundedLatticeHom.map_fourWayDecomposition (e : BoundedLatticeHom α β) e.injective h

theorem fourWayDecomposition_iff (e : α ≃o β) {a w x y z : α} :
    FourWayDecomposition (e a) (e w) (e x) (e y) (e z) ↔
      FourWayDecomposition a w x y z := by
  constructor
  · intro h
    have hp :=
      map_fourWayDecomposition e.symm
        (a := e a) (w := e w) (x := e x) (y := e y) (z := e z) h
    simpa using hp
  · exact map_fourWayDecomposition e

end BooleanAlgebra

end OrderIso

end LeanMathlib
