import LeanMathlib.Order.BooleanModalTheoryQuotient

namespace LeanMathlib

namespace Relational

variable {α σ : Type*}

/--
Modal evaluation factored through the modal-theory quotient.

This interprets formulas directly as sets of theory classes rather than sets of
states.
-/
def quotientEval (r : α → α → Prop) (ν : σ → Set α) :
    ModalFormula σ → Set (TheoryQuotient r ν)
  | .atom p => theoryClass r ν (.atom p)
  | .bot => ∅
  | .compl φ => (quotientEval r ν φ)ᶜ
  | .sup φ ψ => quotientEval r ν φ ∪ quotientEval r ν ψ
  | .diamond φ => theoryClass r ν (.diamond φ)

@[simp] theorem quotientEval_atom (r : α → α → Prop) (ν : σ → Set α) (p : σ) :
    quotientEval r ν (.atom p) = theoryClass r ν (.atom p) := rfl

@[simp] theorem quotientEval_bot (r : α → α → Prop) (ν : σ → Set α) :
    quotientEval r ν .bot = ∅ := rfl

@[simp] theorem quotientEval_compl (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) :
    quotientEval r ν (.compl φ) = (quotientEval r ν φ)ᶜ := rfl

@[simp] theorem quotientEval_sup (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : ModalFormula σ) :
    quotientEval r ν (.sup φ ψ) = quotientEval r ν φ ∪ quotientEval r ν ψ := rfl

@[simp] theorem quotientEval_diamond (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) :
    quotientEval r ν (.diamond φ) = theoryClass r ν (.diamond φ) := rfl

theorem quotientEval_eq_theoryClass (r : α → α → Prop) (ν : σ → Set α) :
    ∀ φ : ModalFormula σ, quotientEval r ν φ = theoryClass r ν φ
  | .atom p => rfl
  | .bot => by
      rw [quotientEval_bot, theoryClass_bot]
  | .compl φ => by
      rw [quotientEval_compl, quotientEval_eq_theoryClass r ν φ, theoryClass_compl]
  | .sup φ ψ => by
      rw [quotientEval_sup, quotientEval_eq_theoryClass r ν φ,
        quotientEval_eq_theoryClass r ν ψ, theoryClass_sup]
  | .diamond φ => rfl

@[simp] theorem mem_quotientEval_mk_iff
    (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) (a : α) :
    theoryQuotientMk r ν a ∈ quotientEval r ν φ ↔ Satisfies r ν a φ := by
  rw [quotientEval_eq_theoryClass, mem_theoryClass_mk_iff]

/-- Quotient-level satisfaction relation. -/
def QuotientSatisfies (r : α → α → Prop) (ν : σ → Set α)
    (q : TheoryQuotient r ν) (φ : ModalFormula σ) : Prop :=
  q ∈ quotientEval r ν φ

@[simp] theorem quotientSatisfies_mk_iff
    (r : α → α → Prop) (ν : σ → Set α)
    (a : α) (φ : ModalFormula σ) :
    QuotientSatisfies r ν (theoryQuotientMk r ν a) φ ↔ Satisfies r ν a φ := by
  exact mem_quotientEval_mk_iff r ν φ a

@[simp] theorem quotientEval_inf (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : ModalFormula σ) :
    quotientEval r ν (ModalFormula.inf φ ψ) =
      quotientEval r ν φ ∩ quotientEval r ν ψ := by
  rw [quotientEval_eq_theoryClass, theoryClass_inf,
    quotientEval_eq_theoryClass, quotientEval_eq_theoryClass]

@[simp] theorem quotientEval_top (r : α → α → Prop) (ν : σ → Set α) :
    quotientEval r ν ModalFormula.top = Set.univ := by
  rw [quotientEval_eq_theoryClass, theoryClass_top]

@[simp] theorem quotientEval_box (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) :
    quotientEval r ν (ModalFormula.box φ) = theoryClass r ν (ModalFormula.box φ) := by
  rw [quotientEval_eq_theoryClass]

theorem quotientSatisfies_wellDefined
    {r : α → α → Prop} {ν : σ → Set α} {a b : α}
    (hab : theoryQuotientMk r ν a = theoryQuotientMk r ν b)
    (φ : ModalFormula σ) :
    QuotientSatisfies r ν (theoryQuotientMk r ν a) φ ↔
      QuotientSatisfies r ν (theoryQuotientMk r ν b) φ := by
  simpa [QuotientSatisfies] using congrArg (fun q => q ∈ quotientEval r ν φ) hab

theorem quotientEval_ext
    {r : α → α → Prop} {ν : σ → Set α} {φ ψ : ModalFormula σ}
    (h : theoryClass r ν φ = theoryClass r ν ψ) :
    quotientEval r ν φ = quotientEval r ν ψ := by
  rw [quotientEval_eq_theoryClass, quotientEval_eq_theoryClass, h]

theorem theoryQuotientMk_eq_of_formula_agreement
    {r : α → α → Prop} {ν : σ → Set α} {a b : α}
    (h :
      ∀ φ : ModalFormula σ,
        QuotientSatisfies r ν (theoryQuotientMk r ν a) φ ↔
          QuotientSatisfies r ν (theoryQuotientMk r ν b) φ) :
    theoryQuotientMk r ν a = theoryQuotientMk r ν b := by
  exact (theoryQuotientMk_eq_iff_formula_membership).2 (fun φ => by
    simpa [QuotientSatisfies] using h φ)

end Relational

end LeanMathlib
