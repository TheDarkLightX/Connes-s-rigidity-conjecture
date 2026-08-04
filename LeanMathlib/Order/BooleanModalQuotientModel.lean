import LeanMathlib.Order.BooleanModalQuotientRelation

namespace LeanMathlib

namespace Relational

variable {α σ : Type*}

/-- Atomic valuation induced on the modal theory quotient. -/
def quotientValuation (r : α → α → Prop) (ν : σ → Set α) (p : σ) :
    Set (TheoryQuotient r ν) :=
  theoryClass r ν (.atom p)

@[simp] theorem quotientValuation_atom (r : α → α → Prop) (ν : σ → Set α) (p : σ) :
    quotientValuation r ν p = theoryClass r ν (.atom p) :=
  rfl

/--
Generic modal evaluation on the quotient transition system agrees with the
factorized quotient semantics built directly from theory classes.
-/
theorem quotientModelEval_eq_quotientEval
    (r : α → α → Prop) (ν : σ → Set α) :
    ∀ φ : ModalFormula σ,
      eval (RepresentativeStep r ν) (quotientValuation r ν) φ = quotientEval r ν φ
  | .atom p => rfl
  | .bot => rfl
  | .compl φ => by
      rw [eval_compl, quotientModelEval_eq_quotientEval r ν φ, quotientEval_compl]
  | .sup φ ψ => by
      rw [eval_sup, quotientModelEval_eq_quotientEval r ν φ,
        quotientModelEval_eq_quotientEval r ν ψ, quotientEval_sup]
  | .diamond φ => by
      ext q
      rw [eval_diamond, quotientModelEval_eq_quotientEval r ν φ]
      constructor
      · intro hq
        rcases (mem_diamond_iff
          (r := converse (RepresentativeStep r ν))
          (s := quotientEval r ν φ) (b := q)).1 hq with ⟨q', hq', hstep⟩
        rw [quotientEval_diamond_eq_successor r ν φ]
        exact ⟨q', hstep, hq'⟩
      · intro hq
        rw [quotientEval_diamond_eq_successor r ν φ] at hq
        rcases hq with ⟨q', hstep, hq'⟩
        exact (mem_diamond_iff
          (r := converse (RepresentativeStep r ν))
          (s := quotientEval r ν φ) (b := q)).2 ⟨q', hq', hstep⟩

/-- Quotient-model satisfaction phrased through the actual quotient transition relation. -/
def QuotientModelSatisfies (r : α → α → Prop) (ν : σ → Set α)
    (q : TheoryQuotient r ν) (φ : ModalFormula σ) : Prop :=
  Satisfies (RepresentativeStep r ν) (quotientValuation r ν) q φ

@[simp] theorem quotientModelSatisfies_iff_quotientSatisfies
    (r : α → α → Prop) (ν : σ → Set α)
    (q : TheoryQuotient r ν) (φ : ModalFormula σ) :
    QuotientModelSatisfies r ν q φ ↔ QuotientSatisfies r ν q φ := by
  change q ∈ eval (RepresentativeStep r ν) (quotientValuation r ν) φ ↔
    q ∈ quotientEval r ν φ
  rw [quotientModelEval_eq_quotientEval]

@[simp] theorem quotientModelSatisfies_mk_iff
    (r : α → α → Prop) (ν : σ → Set α)
    (a : α) (φ : ModalFormula σ) :
    QuotientModelSatisfies r ν (theoryQuotientMk r ν a) φ ↔ Satisfies r ν a φ := by
  rw [quotientModelSatisfies_iff_quotientSatisfies, quotientSatisfies_mk_iff]

@[simp] theorem quotientModelEval_box
    (r : α → α → Prop) (ν : σ → Set α) (φ : ModalFormula σ) :
    eval (RepresentativeStep r ν) (quotientValuation r ν) (ModalFormula.box φ) =
      quotientEval r ν (ModalFormula.box φ) := by
  rw [quotientModelEval_eq_quotientEval]

@[simp] theorem quotientModelEval_top
    (r : α → α → Prop) (ν : σ → Set α) :
    eval (RepresentativeStep r ν) (quotientValuation r ν) ModalFormula.top = Set.univ := by
  rw [quotientModelEval_eq_quotientEval, quotientEval_top]

theorem quotientModelSatisfies_wellDefined
    {r : α → α → Prop} {ν : σ → Set α} {q q' : TheoryQuotient r ν}
    (hqq' : q = q') (φ : ModalFormula σ) :
    QuotientModelSatisfies r ν q φ ↔ QuotientModelSatisfies r ν q' φ := by
  cases hqq'
  exact Iff.rfl

end Relational

end LeanMathlib
