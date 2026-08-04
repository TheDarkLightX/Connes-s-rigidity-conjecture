import LeanMathlib.Order.BooleanModalQuotientFactorization

namespace LeanMathlib

namespace Relational

variable {α σ : Type*}

/--
Quotient-level transition relation induced by the existence of a representative
step in the original frame.
-/
def RepresentativeStep (r : α → α → Prop) (ν : σ → Set α)
    (q q' : TheoryQuotient r ν) : Prop :=
  ∃ a b, theoryQuotientMk r ν a = q ∧ theoryQuotientMk r ν b = q' ∧ r a b

theorem representativeStep_of_step
    {r : α → α → Prop} {ν : σ → Set α} {a b : α}
    (hab : r a b) :
    RepresentativeStep r ν (theoryQuotientMk r ν a) (theoryQuotientMk r ν b) := by
  exact ⟨a, b, rfl, rfl, hab⟩

theorem quotientSatisfies_diamond_iff_exists_representativeStep
    (r : α → α → Prop) (ν : σ → Set α)
    (q : TheoryQuotient r ν) (φ : ModalFormula σ) :
    QuotientSatisfies r ν q (.diamond φ) ↔
      ∃ q', RepresentativeStep r ν q q' ∧ QuotientSatisfies r ν q' φ := by
  refine Quotient.inductionOn q ?_
  intro a
  constructor
  · intro hq
    have ha : Satisfies r ν a (.diamond φ) :=
      (quotientSatisfies_mk_iff r ν a (.diamond φ)).1 hq
    rcases (mem_diamond_iff (r := converse r) (s := eval r ν φ) (b := a)).1 ha with ⟨b, hb, hr⟩
    refine ⟨theoryQuotientMk r ν b, ?_, ?_⟩
    · exact representativeStep_of_step (ν := ν) hr
    · exact (quotientSatisfies_mk_iff r ν b φ).2 hb
  · rintro ⟨q', hstep, hq'⟩
    rcases hstep with ⟨a', b, ha', hb, hr⟩
    have hbSat : Satisfies r ν b φ := by
      have hq'b : QuotientSatisfies r ν (theoryQuotientMk r ν b) φ := by
        simpa [hb] using hq'
      exact (quotientSatisfies_mk_iff r ν b φ).1 hq'b
    have ha'Sat : QuotientSatisfies r ν (theoryQuotientMk r ν a') (.diamond φ) := by
      apply (quotientSatisfies_mk_iff r ν a' (.diamond φ)).2
      exact (mem_diamond_iff (r := converse r) (s := eval r ν φ) (b := a')).2 ⟨b, hbSat, hr⟩
    simpa [ha'] using ha'Sat

theorem quotientEval_diamond_eq_successor
    (r : α → α → Prop) (ν : σ → Set α) (φ : ModalFormula σ) :
    quotientEval r ν (.diamond φ) =
      { q | ∃ q', RepresentativeStep r ν q q' ∧ q' ∈ quotientEval r ν φ } := by
  ext q
  exact quotientSatisfies_diamond_iff_exists_representativeStep r ν q φ

theorem quotientSatisfies_box_iff_forall_representativeStep
    (r : α → α → Prop) (ν : σ → Set α)
    (q : TheoryQuotient r ν) (φ : ModalFormula σ) :
    QuotientSatisfies r ν q (ModalFormula.box φ) ↔
      ∀ q', RepresentativeStep r ν q q' → QuotientSatisfies r ν q' φ := by
  refine Quotient.inductionOn q ?_
  intro a
  constructor
  · intro hq q' hstep
    rcases hstep with ⟨a', b, ha', hb, hr⟩
    have ha'Box : QuotientSatisfies r ν (theoryQuotientMk r ν a') (ModalFormula.box φ) := by
      simpa [ha'] using hq
    have hStateBox : Satisfies r ν a' (ModalFormula.box φ) :=
      (quotientSatisfies_mk_iff r ν a' (ModalFormula.box φ)).1 ha'Box
    have hbSat : Satisfies r ν b φ := by
      exact (mem_box_iff (r := converse r) (s := eval r ν φ) (b := a')).1
        (by simpa [Satisfies, eval_box] using hStateBox) b hr
    have hq'b : QuotientSatisfies r ν (theoryQuotientMk r ν b) φ :=
      (quotientSatisfies_mk_iff r ν b φ).2 hbSat
    simpa [hb] using hq'b
  · intro hAll
    apply (quotientSatisfies_mk_iff r ν a (ModalFormula.box φ)).2
    change a ∈ box (converse r) (eval r ν φ)
    rw [mem_box_iff (r := converse r) (s := eval r ν φ) (b := a)]
    intro b hr
    have hStep : RepresentativeStep r ν (theoryQuotientMk r ν a) (theoryQuotientMk r ν b) :=
      representativeStep_of_step (ν := ν) hr
    have hq' : QuotientSatisfies r ν (theoryQuotientMk r ν b) φ := hAll _ hStep
    exact (quotientSatisfies_mk_iff r ν b φ).1 hq'

theorem quotientEval_box_eq_universal
    (r : α → α → Prop) (ν : σ → Set α) (φ : ModalFormula σ) :
    quotientEval r ν (ModalFormula.box φ) =
      { q | ∀ q', RepresentativeStep r ν q q' → q' ∈ quotientEval r ν φ } := by
  ext q
  exact quotientSatisfies_box_iff_forall_representativeStep r ν q φ

end Relational

end LeanMathlib
