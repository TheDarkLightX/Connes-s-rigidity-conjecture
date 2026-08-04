import LeanMathlib.Order.StoneQuotientClopen
import Mathlib.Order.BooleanSubalgebra

namespace LeanMathlib

open Filter

namespace Stone

variable {α σ : Type*}

@[simp] theorem formulaClopen_bot
    (r : α → α → Prop) (ν : σ → Set α) :
    formulaClopen r ν .bot = (⊥ : Set (Ultrafilter (Relational.TheoryQuotient r ν))) := by
  ext u
  simp [formulaClopen]

@[simp] theorem formulaClopen_top
    (r : α → α → Prop) (ν : σ → Set α) :
    formulaClopen r ν Relational.ModalFormula.top = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    rw [formulaClopen, Relational.quotientEval_top]
    exact Filter.univ_mem

@[simp] theorem formulaClopen_sup
    (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : Relational.ModalFormula σ) :
    formulaClopen r ν (.sup φ ψ) =
      formulaClopen r ν φ ∪ formulaClopen r ν ψ := by
  ext u
  simp [formulaClopen]

@[simp] theorem formulaClopen_inf
    (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : Relational.ModalFormula σ) :
    formulaClopen r ν (Relational.ModalFormula.inf φ ψ) =
      formulaClopen r ν φ ∩ formulaClopen r ν ψ := by
  ext u
  change (Relational.quotientEval r ν (Relational.ModalFormula.inf φ ψ) ∈ u ↔
      Relational.quotientEval r ν φ ∈ u ∧ Relational.quotientEval r ν ψ ∈ u)
  rw [Relational.quotientEval_inf]
  exact Filter.inter_mem_iff

@[simp] theorem formulaClopen_compl
    (r : α → α → Prop) (ν : σ → Set α)
    (φ : Relational.ModalFormula σ) :
    formulaClopen r ν (.compl φ) = (formulaClopen r ν φ)ᶜ := by
  ext u
  simp [formulaClopen, Ultrafilter.compl_mem_iff_notMem]

/-- The Boolean subalgebra of Stone clopens cut out by modal formulas on the quotient. -/
def formulaClopenSubalgebra (r : α → α → Prop) (ν : σ → Set α) :
    BooleanSubalgebra (Set (Ultrafilter (Relational.TheoryQuotient r ν))) where
  carrier := { s | ∃ φ : Relational.ModalFormula σ, s = formulaClopen r ν φ }
  bot_mem' := ⟨.bot, (formulaClopen_bot r ν).symm⟩
  compl_mem' := by
    intro s hs
    rcases hs with ⟨φ, rfl⟩
    exact ⟨.compl φ, (formulaClopen_compl r ν φ).symm⟩
  supClosed' := by
    intro a ha b hb
    rcases ha with ⟨φ, rfl⟩
    rcases hb with ⟨ψ, rfl⟩
    exact ⟨.sup φ ψ, (formulaClopen_sup r ν φ ψ).symm⟩
  infClosed' := by
    intro a ha b hb
    rcases ha with ⟨φ, rfl⟩
    rcases hb with ⟨ψ, rfl⟩
    exact ⟨Relational.ModalFormula.inf φ ψ, (formulaClopen_inf r ν φ ψ).symm⟩

@[simp] theorem mem_formulaClopenSubalgebra
    (r : α → α → Prop) (ν : σ → Set α)
    {s : Set (Ultrafilter (Relational.TheoryQuotient r ν))} :
    s ∈ formulaClopenSubalgebra r ν ↔
      ∃ φ : Relational.ModalFormula σ, s = formulaClopen r ν φ := by
  rfl

theorem formulaClopen_mem_formulaClopenSubalgebra
    (r : α → α → Prop) (ν : σ → Set α)
    (φ : Relational.ModalFormula σ) :
    formulaClopen r ν φ ∈ formulaClopenSubalgebra r ν :=
  ⟨φ, rfl⟩

theorem isClopen_of_mem_formulaClopenSubalgebra
    {r : α → α → Prop} {ν : σ → Set α}
    {s : Set (Ultrafilter (Relational.TheoryQuotient r ν))}
    (hs : s ∈ formulaClopenSubalgebra r ν) :
    IsClopen s := by
  rcases hs with ⟨φ, rfl⟩
  exact isClopen_formulaClopen r ν φ

theorem quotientState_ne_iff_exists_formulaClopenSubalgebra_separator
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : Relational.TheoryQuotient r ν) :
    q ≠ q' ↔
      ∃ s ∈ formulaClopenSubalgebra r ν,
        ((principalPoint q ∈ s ∧ principalPoint q' ∉ s) ∨
          (principalPoint q' ∈ s ∧ principalPoint q ∉ s)) := by
  constructor
  · intro hNe
    rcases (quotientState_ne_iff_exists_formulaClopen_separator r ν q q').1 hNe with
      ⟨φ, hφ⟩
    exact ⟨formulaClopen r ν φ, formulaClopen_mem_formulaClopenSubalgebra r ν φ, hφ⟩
  · rintro ⟨s, hs, hsep⟩ hEq
    rcases hs with ⟨φ, rfl⟩
    exact (quotientState_ne_iff_exists_formulaClopen_separator r ν q q').2 ⟨φ, hsep⟩ hEq

theorem quotientState_eq_iff_forall_formulaClopenSubalgebra_membership
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : Relational.TheoryQuotient r ν) :
    q = q' ↔
      ∀ s ∈ formulaClopenSubalgebra r ν,
        (principalPoint q ∈ s ↔ principalPoint q' ∈ s) := by
  constructor
  · intro hEq s hs
    simp [hEq]
  · intro hAgree
    by_contra hNe
    rcases (quotientState_ne_iff_exists_formulaClopenSubalgebra_separator r ν q q').1 hNe with
      ⟨s, hs, (⟨hq, hq'⟩ | ⟨hq', hq⟩)⟩
    · exact hq' ((hAgree s hs).1 hq)
    · exact hq ((hAgree s hs).2 hq')

end Stone

end LeanMathlib
