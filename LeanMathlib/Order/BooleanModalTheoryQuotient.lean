import LeanMathlib.Order.BooleanModalFormulaInvariance

namespace LeanMathlib

namespace Relational

variable {α β σ : Type*}

/-- Modal-theory equivalence: two states satisfy exactly the same formulas. -/
def TheoryEq (r : α → α → Prop) (ν : σ → Set α) (a b : α) : Prop :=
  ∀ φ : ModalFormula σ, Satisfies r ν a φ ↔ Satisfies r ν b φ

theorem theoryEq_refl (r : α → α → Prop) (ν : σ → Set α) (a : α) :
    TheoryEq r ν a a := by
  intro φ
  rfl

theorem theoryEq_symm {r : α → α → Prop} {ν : σ → Set α} {a b : α}
    (h : TheoryEq r ν a b) :
    TheoryEq r ν b a := by
  intro φ
  exact (h φ).symm

theorem theoryEq_trans {r : α → α → Prop} {ν : σ → Set α} {a b c : α}
    (hab : TheoryEq r ν a b) (hbc : TheoryEq r ν b c) :
    TheoryEq r ν a c := by
  intro φ
  exact (hab φ).trans (hbc φ)

/-- The modal-theory setoid of a fixed relational model. -/
def theorySetoid (r : α → α → Prop) (ν : σ → Set α) : Setoid α where
  r := TheoryEq r ν
  iseqv := ⟨theoryEq_refl r ν, theoryEq_symm, theoryEq_trans⟩

/-- Quotient of states by modal-theory equivalence. -/
abbrev TheoryQuotient (r : α → α → Prop) (ν : σ → Set α) :=
  Quotient (theorySetoid r ν)

/-- Canonical quotient map to theory classes. -/
def theoryQuotientMk (r : α → α → Prop) (ν : σ → Set α) (a : α) :
    TheoryQuotient r ν :=
  Quotient.mk (theorySetoid r ν) a

theorem theoryQuotientMk_eq_iff {r : α → α → Prop} {ν : σ → Set α} {a b : α} :
    theoryQuotientMk r ν a = theoryQuotientMk r ν b ↔ TheoryEq r ν a b := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/--
The quotient class cut out by a modal formula. This is well-defined because
formula truth is constant on modal-theory classes.
-/
def theoryClass (r : α → α → Prop) (ν : σ → Set α) (φ : ModalFormula σ) :
    Set (TheoryQuotient r ν) :=
  fun q =>
    Quotient.liftOn q (fun a => Satisfies r ν a φ)
      (by
        intro a b hab
        exact propext (hab φ))

@[simp] theorem mem_theoryClass_mk_iff
    (r : α → α → Prop) (ν : σ → Set α) (φ : ModalFormula σ) (a : α) :
    theoryQuotientMk r ν a ∈ theoryClass r ν φ ↔ Satisfies r ν a φ := by
  rfl

theorem theoryEq_iff_formula_membership
    {r : α → α → Prop} {ν : σ → Set α} {a b : α} :
    TheoryEq r ν a b ↔
      ∀ φ : ModalFormula σ,
        theoryQuotientMk r ν a ∈ theoryClass r ν φ ↔
          theoryQuotientMk r ν b ∈ theoryClass r ν φ := by
  constructor
  · intro h φ
    simpa [mem_theoryClass_mk_iff] using h φ
  · intro h φ
    simpa [mem_theoryClass_mk_iff] using h φ

theorem theoryQuotientMk_eq_iff_formula_membership
    {r : α → α → Prop} {ν : σ → Set α} {a b : α} :
    theoryQuotientMk r ν a = theoryQuotientMk r ν b ↔
      ∀ φ : ModalFormula σ,
        theoryQuotientMk r ν a ∈ theoryClass r ν φ ↔
          theoryQuotientMk r ν b ∈ theoryClass r ν φ := by
  rw [theoryQuotientMk_eq_iff, theoryEq_iff_formula_membership]

@[simp] theorem theoryClass_bot (r : α → α → Prop) (ν : σ → Set α) :
    theoryClass r ν .bot = ∅ := by
  ext q
  refine Quotient.inductionOn q ?_
  intro a
  change theoryQuotientMk r ν a ∈ theoryClass r ν .bot ↔ False
  simp [mem_theoryClass_mk_iff, Satisfies]

@[simp] theorem theoryClass_sup
    (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : ModalFormula σ) :
    theoryClass r ν (.sup φ ψ) = theoryClass r ν φ ∪ theoryClass r ν ψ := by
  ext q
  refine Quotient.inductionOn q ?_
  intro a
  change theoryQuotientMk r ν a ∈ theoryClass r ν (.sup φ ψ) ↔
      theoryQuotientMk r ν a ∈ theoryClass r ν φ ∨
        theoryQuotientMk r ν a ∈ theoryClass r ν ψ
  simp [mem_theoryClass_mk_iff, Satisfies]

@[simp] theorem theoryClass_compl
    (r : α → α → Prop) (ν : σ → Set α)
    (φ : ModalFormula σ) :
    theoryClass r ν (.compl φ) = (theoryClass r ν φ)ᶜ := by
  ext q
  refine Quotient.inductionOn q ?_
  intro a
  change theoryQuotientMk r ν a ∈ theoryClass r ν (.compl φ) ↔
      theoryQuotientMk r ν a ∉ theoryClass r ν φ
  simp [mem_theoryClass_mk_iff, Satisfies]

@[simp] theorem theoryClass_inf
    (r : α → α → Prop) (ν : σ → Set α)
    (φ ψ : ModalFormula σ) :
    theoryClass r ν (ModalFormula.inf φ ψ) =
      theoryClass r ν φ ∩ theoryClass r ν ψ := by
  ext q
  refine Quotient.inductionOn q ?_
  intro a
  change theoryQuotientMk r ν a ∈ theoryClass r ν (ModalFormula.inf φ ψ) ↔
      theoryQuotientMk r ν a ∈ theoryClass r ν φ ∧
        theoryQuotientMk r ν a ∈ theoryClass r ν ψ
  simp [mem_theoryClass_mk_iff, Satisfies]

@[simp] theorem theoryClass_top
    (r : α → α → Prop) (ν : σ → Set α) :
    theoryClass r ν ModalFormula.top = Set.univ := by
  ext q
  refine Quotient.inductionOn q ?_
  intro a
  change theoryQuotientMk r ν a ∈ theoryClass r ν ModalFormula.top ↔ True
  simp [mem_theoryClass_mk_iff, Satisfies]

theorem theoryEq_of_bisimulation
    {z : α → β → Prop} {r : α → α → Prop} {s : β → β → Prop}
    (hbisim : IsBisimulation z r s)
    {να : σ → Set α} {νβ : σ → Set β}
    (hval : ∀ p, Respects z (να p) (νβ p))
    {a : α} {b : β} (hz : z a b) :
    ∀ φ : ModalFormula σ, Satisfies r να a φ ↔ Satisfies s νβ b φ := by
  intro φ
  exact satisfies_iff_of_bisimulation hbisim hval hz φ

theorem theoryEq_self_of_bisimulation
    {z : α → α → Prop} {r : α → α → Prop}
    (hbisim : IsBisimulation z r r)
    {ν : σ → Set α}
    (hval : ∀ p, Respects z (ν p) (ν p))
    {a b : α} (hz : z a b) :
    TheoryEq r ν a b := by
  intro φ
  exact satisfies_iff_of_bisimulation hbisim hval hz φ

theorem theoryQuotientMk_eq_of_bisimulation
    {z : α → α → Prop} {r : α → α → Prop}
    (hbisim : IsBisimulation z r r)
    {ν : σ → Set α}
    (hval : ∀ p, Respects z (ν p) (ν p))
    {a b : α} (hz : z a b) :
    theoryQuotientMk r ν a = theoryQuotientMk r ν b := by
  exact Quotient.sound (theoryEq_self_of_bisimulation hbisim hval hz)

end Relational

end LeanMathlib
