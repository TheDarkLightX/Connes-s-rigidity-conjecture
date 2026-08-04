import LeanMathlib.Order.BooleanModalQuotientCanonical
import LeanMathlib.Order.StoneBasicClopen

namespace LeanMathlib

open Filter

namespace Stone

variable {α σ : Type*}

/-- The Stone basic clopen determined by a formula on the modal-theory quotient. -/
def formulaClopen (r : α → α → Prop) (ν : σ → Set α)
    (φ : Relational.ModalFormula σ) :
    Set (Ultrafilter (Relational.TheoryQuotient r ν)) :=
  basicClopen (Relational.quotientEval r ν φ)

@[simp] theorem mem_formulaClopen_iff
    {r : α → α → Prop} {ν : σ → Set α}
    {φ : Relational.ModalFormula σ}
    {u : Ultrafilter (Relational.TheoryQuotient r ν)} :
    u ∈ formulaClopen r ν φ ↔ Relational.quotientEval r ν φ ∈ u := by
  rfl

theorem isClopen_formulaClopen
    (r : α → α → Prop) (ν : σ → Set α)
    (φ : Relational.ModalFormula σ) :
    IsClopen (formulaClopen r ν φ) :=
  isClopen_basicClopen _

@[simp] theorem principalPoint_mem_formulaClopen_iff
    (r : α → α → Prop) (ν : σ → Set α)
    (q : Relational.TheoryQuotient r ν) (φ : Relational.ModalFormula σ) :
    principalPoint q ∈ formulaClopen r ν φ ↔
      Relational.QuotientSatisfies r ν q φ := by
  simp [formulaClopen, Relational.QuotientSatisfies]

@[simp] theorem principalPoint_mem_formulaClopen_iff_quotientModelSatisfies
    (r : α → α → Prop) (ν : σ → Set α)
    (q : Relational.TheoryQuotient r ν) (φ : Relational.ModalFormula σ) :
    principalPoint q ∈ formulaClopen r ν φ ↔
      Relational.QuotientModelSatisfies r ν q φ := by
  rw [Relational.quotientModelSatisfies_iff_quotientSatisfies]
  exact principalPoint_mem_formulaClopen_iff r ν q φ

@[simp] theorem principalPoint_mem_formulaClopen_mk_iff
    (r : α → α → Prop) (ν : σ → Set α)
    (a : α) (φ : Relational.ModalFormula σ) :
    principalPoint (Relational.theoryQuotientMk r ν a) ∈ formulaClopen r ν φ ↔
      Relational.Satisfies r ν a φ := by
  simp [formulaClopen]

theorem formulaClopen_eq_iff
    (r : α → α → Prop) (ν : σ → Set α)
    {φ ψ : Relational.ModalFormula σ} :
    formulaClopen r ν φ = formulaClopen r ν ψ ↔
      Relational.quotientEval r ν φ = Relational.quotientEval r ν ψ := by
  rw [formulaClopen, formulaClopen, basicClopen_eq_iff]

theorem quotientState_eq_iff_forall_formulaClopen_membership
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : Relational.TheoryQuotient r ν) :
    q = q' ↔
      ∀ φ : Relational.ModalFormula σ,
        (principalPoint q ∈ formulaClopen r ν φ ↔
          principalPoint q' ∈ formulaClopen r ν φ) := by
  constructor
  · intro hEq φ
    simp [hEq]
  · intro hmem
    exact (Relational.quotientModel_eq_iff_formula_agreement r ν q q').2 <|
      fun φ => by
        simpa using hmem φ

theorem quotientState_ne_iff_exists_formulaClopen_separator
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : Relational.TheoryQuotient r ν) :
    q ≠ q' ↔
      ∃ φ : Relational.ModalFormula σ,
        ((principalPoint q ∈ formulaClopen r ν φ ∧
            principalPoint q' ∉ formulaClopen r ν φ) ∨
          (principalPoint q' ∈ formulaClopen r ν φ ∧
            principalPoint q ∉ formulaClopen r ν φ)) := by
  constructor
  · intro hNe
    rcases (Relational.quotientModel_ne_iff_exists_formula_difference r ν q q').1 hNe with
      ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    simpa using hφ
  · rintro ⟨φ, (⟨hq, hq'⟩ | ⟨hq', hq⟩)⟩ hEq
    · exact hq' (hEq ▸ hq)
    · exact hq (hEq ▸ hq')

theorem quotientState_eq_iff_forall_formulaClopen_eq
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : Relational.TheoryQuotient r ν) :
    q = q' ↔
      ∀ φ : Relational.ModalFormula σ,
        (principalPoint q ∈ formulaClopen r ν φ) =
          (principalPoint q' ∈ formulaClopen r ν φ) := by
  constructor
  · intro hEq φ
    simp [hEq]
  · intro hEq
    exact (quotientState_eq_iff_forall_formulaClopen_membership r ν q q').2 <|
      fun φ => Iff.of_eq (hEq φ)

end Stone

end LeanMathlib
