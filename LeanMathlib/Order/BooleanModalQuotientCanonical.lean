import LeanMathlib.Order.BooleanModalQuotientModel

namespace LeanMathlib

namespace Relational

variable {α σ : Type*}

theorem theoryQuotient_surjective
    (r : α → α → Prop) (ν : σ → Set α) :
    Function.Surjective (theoryQuotientMk r ν) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  exact ⟨a, rfl⟩

theorem quotientModel_eq_iff_formula_agreement
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : TheoryQuotient r ν) :
    q = q' ↔
      ∀ φ : ModalFormula σ,
        QuotientModelSatisfies r ν q φ ↔ QuotientModelSatisfies r ν q' φ := by
  constructor
  · intro hEq φ
    cases hEq
    exact Iff.rfl
  · revert q'
    refine Quotient.inductionOn q ?_
    intro a q'
    refine Quotient.inductionOn q' ?_
    intro b hAgree
    exact theoryQuotientMk_eq_of_formula_agreement (r := r) (ν := ν) (a := a) (b := b) <|
      fun φ => by
        rw [← quotientModelSatisfies_iff_quotientSatisfies,
          ← quotientModelSatisfies_iff_quotientSatisfies]
        exact hAgree φ

theorem quotientModel_ne_iff_exists_formula_separator
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : TheoryQuotient r ν) :
    q ≠ q' ↔
      ∃ φ : ModalFormula σ,
        ¬ (QuotientModelSatisfies r ν q φ ↔ QuotientModelSatisfies r ν q' φ) := by
  constructor
  · intro hNe
    classical
    by_contra hNoSep
    apply hNe
    exact (quotientModel_eq_iff_formula_agreement r ν q q').2 <|
      fun φ => by
        by_contra hiff
        exact hNoSep ⟨φ, hiff⟩
  · rintro ⟨φ, hSep⟩ hEq
    apply hSep
    cases hEq
    exact Iff.rfl

theorem quotientModel_ne_iff_exists_formula_difference
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : TheoryQuotient r ν) :
    q ≠ q' ↔
      ∃ φ : ModalFormula σ,
        (QuotientModelSatisfies r ν q φ ∧ ¬ QuotientModelSatisfies r ν q' φ) ∨
          (QuotientModelSatisfies r ν q' φ ∧ ¬ QuotientModelSatisfies r ν q φ) := by
  constructor
  · intro hNe
    rcases (quotientModel_ne_iff_exists_formula_separator r ν q q').1 hNe with ⟨φ, hSep⟩
    by_cases hq : QuotientModelSatisfies r ν q φ
    · refine ⟨φ, Or.inl ?_⟩
      refine ⟨hq, ?_⟩
      intro hq'
      apply hSep
      exact Iff.intro (fun _ => hq') (fun _ => hq)
    · refine ⟨φ, Or.inr ?_⟩
      by_cases hq' : QuotientModelSatisfies r ν q' φ
      · exact ⟨hq', hq⟩
      · exfalso
        apply hSep
        exact Iff.intro (fun h => False.elim (hq h)) (fun h => False.elim (hq' h))
  · rintro ⟨φ, hdiff⟩ hEq
    rcases hdiff with ⟨hq, hq'⟩ | ⟨hq', hq⟩
    · exact hq' (hEq ▸ hq)
    · exact hq (hEq ▸ hq')

theorem quotientModel_eq_iff_atom_formula_agreement_of_formula_complete
    (r : α → α → Prop) (ν : σ → Set α)
    (q q' : TheoryQuotient r ν)
    (hcomplete :
      ∀ φ : ModalFormula σ,
        QuotientModelSatisfies r ν q φ ↔ QuotientModelSatisfies r ν q' φ) :
    q = q' :=
  (quotientModel_eq_iff_formula_agreement r ν q q').2 hcomplete

end Relational

end LeanMathlib
