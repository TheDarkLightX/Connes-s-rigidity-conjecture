import LeanMathlib.Order.BooleanPartition

namespace LeanMathlib

namespace BoundedLatticeHom

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem map_ne_bot_of_injective (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) {x : α} (hx : x ≠ ⊥) :
    f x ≠ ⊥ := by
  intro hfx
  apply hx
  apply hf
  rw [hfx, map_bot]

theorem map_disjoint (f : BoundedLatticeHom α β) {x y : α}
    (hxy : Disjoint x y) :
    Disjoint (f x) (f y) := by
  rw [disjoint_iff]
  apply le_bot_iff.mp
  calc
    f x ⊓ f y = f (x ⊓ y) := by simp
    _ ≤ ⊥ := by
      rw [hxy.eq_bot, map_bot]

theorem map_twoWayDecomposition (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) {a x y : α}
    (h : TwoWayDecomposition a x y) :
    TwoWayDecomposition (f a) (f x) (f y) where
  left_nonzero := map_ne_bot_of_injective f hf h.left_nonzero
  right_nonzero := map_ne_bot_of_injective f hf h.right_nonzero
  disjoint := map_disjoint f h.disjoint
  sup_eq := by
    calc
      f x ⊔ f y = f (x ⊔ y) := by simp
      _ = f a := by rw [h.sup_eq]

theorem map_threeWayDecomposition (f : BoundedLatticeHom α β)
    (hf : Function.Injective f) {a x y z : α}
    (h : ThreeWayDecomposition a x y z) :
    ThreeWayDecomposition (f a) (f x) (f y) (f z) where
  first_nonzero := map_ne_bot_of_injective f hf h.first_nonzero
  second_nonzero := map_ne_bot_of_injective f hf h.second_nonzero
  third_nonzero := map_ne_bot_of_injective f hf h.third_nonzero
  first_second := map_disjoint f h.first_second
  first_third := map_disjoint f h.first_third
  second_third := map_disjoint f h.second_third
  sup_eq := by
    calc
      (f x ⊔ f y) ⊔ f z = f ((x ⊔ y) ⊔ z) := by simp
      _ = f a := by rw [h.sup_eq]

end BooleanAlgebra

end BoundedLatticeHom

namespace OrderIso

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

theorem map_twoWayDecomposition (e : α ≃o β) {a x y : α}
    (h : TwoWayDecomposition a x y) :
    TwoWayDecomposition (e a) (e x) (e y) :=
  BoundedLatticeHom.map_twoWayDecomposition (e : BoundedLatticeHom α β) e.injective h

theorem map_threeWayDecomposition (e : α ≃o β) {a x y z : α}
    (h : ThreeWayDecomposition a x y z) :
    ThreeWayDecomposition (e a) (e x) (e y) (e z) :=
  BoundedLatticeHom.map_threeWayDecomposition (e : BoundedLatticeHom α β) e.injective h

theorem twoWayDecomposition_iff (e : α ≃o β) {a x y : α} :
    TwoWayDecomposition (e a) (e x) (e y) ↔ TwoWayDecomposition a x y := by
  constructor
  · intro h
    have hp :=
      map_twoWayDecomposition e.symm (a := e a) (x := e x) (y := e y) h
    simpa using hp
  · exact map_twoWayDecomposition e

theorem threeWayDecomposition_iff (e : α ≃o β) {a x y z : α} :
    ThreeWayDecomposition (e a) (e x) (e y) (e z) ↔ ThreeWayDecomposition a x y z := by
  constructor
  · intro h
    have hp :=
      map_threeWayDecomposition e.symm (a := e a) (x := e x) (y := e y) (z := e z) h
    simpa using hp
  · exact map_threeWayDecomposition e

end BooleanAlgebra

end OrderIso

end LeanMathlib
