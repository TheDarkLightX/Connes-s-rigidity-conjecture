import LeanMathlib.FormalMethods.TransitionBarrier

namespace LeanMathlib

namespace FormalMethods

namespace AbstractInterpretation

open TransitionSystem

variable {C A : Type*}

def GaloisConnection [LE C] [LE A] (abst : C → A) (conc : A → C) : Prop :=
  ∀ c a, abst c ≤ a ↔ c ≤ conc a

theorem le_conc_abst [Preorder C] [Preorder A]
    {abst : C → A} {conc : A → C}
    (h : GaloisConnection abst conc) (c : C) :
    c ≤ conc (abst c) :=
  (h c (abst c)).1 le_rfl

theorem abst_conc_le [Preorder C] [Preorder A]
    {abst : C → A} {conc : A → C}
    (h : GaloisConnection abst conc) (a : A) :
    abst (conc a) ≤ a :=
  (h (conc a) a).2 le_rfl

theorem monotone_abst [Preorder C] [Preorder A]
    {abst : C → A} {conc : A → C}
    (h : GaloisConnection abst conc) :
    Monotone abst := by
  intro c d hcd
  exact (h c (abst d)).2 (le_trans hcd (le_conc_abst h d))

theorem monotone_conc [Preorder C] [Preorder A]
    {abst : C → A} {conc : A → C}
    (h : GaloisConnection abst conc) :
    Monotone conc := by
  intro a b hab
  exact (h (conc a) b).1 (le_trans (abst_conc_le h a) hab)

theorem closure_idempotent [PartialOrder C] [Preorder A]
    {abst : C → A} {conc : A → C}
    (h : GaloisConnection abst conc) (c : C) :
    conc (abst (conc (abst c))) = conc (abst c) := by
  apply le_antisymm
  · exact monotone_conc h (abst_conc_le h (abst c))
  · exact le_conc_abst h (conc (abst c))

def iterate (next : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => next (iterate next n a)

def TransformerSound (T : TransitionSystem C)
    (represents : A → C → Prop) (next : A → A) : Prop :=
  ∀ {a : A} {c c' : C}, represents a c → T.Step c c' → represents (next a) c'

def AbstractSafetyBridge (represents : A → C → Prop)
    (safeA : A → Prop) (safeC : C → Prop) : Prop :=
  ∀ {a : A} {c : C}, represents a c → safeA a → safeC c

theorem represents_of_traceN {T : TransitionSystem C}
    {represents : A → C → Prop} {next : A → A}
    (hStep : TransformerSound T represents next)
    {n : Nat} {c c' : C} {a : A}
    (hTrace : T.TraceN n c c') (hInit : represents a c) :
    represents (iterate next n a) c' := by
  induction hTrace generalizing a with
  | nil c =>
      simpa [iterate] using hInit
  | snoc hTrace hStepC ih =>
      simpa [iterate] using hStep (ih hInit) hStepC

theorem concrete_safe_of_abstract_trace {T : TransitionSystem C}
    {represents : A → C → Prop} {next : A → A}
    {safeA : A → Prop} {safeC : C → Prop}
    (hStep : TransformerSound T represents next)
    (hBridge : AbstractSafetyBridge represents safeA safeC)
    {n : Nat} {c c' : C} {a : A}
    (hTrace : T.TraceN n c c')
    (hInit : represents a c)
    (hAbs : safeA (iterate next n a)) :
    safeC c' :=
  hBridge (represents_of_traceN hStep hTrace hInit) hAbs

theorem barrier_from_abstract_trace {T : TransitionSystem C}
    {represents : A → C → Prop} {next : A → A}
    {score : C → A} {cutoff : A} [Preorder A]
    (hStep : TransformerSound T represents next)
    (hBridge : ∀ {a : A} {c : C}, represents a c → cutoff ≤ a → cutoff ≤ score c)
    {n : Nat} {c c' : C} {a : A}
    (hTrace : T.TraceN n c c')
    (hInit : represents a c)
    (hAbs : cutoff ≤ iterate next n a) :
    cutoff ≤ score c' :=
  hBridge (represents_of_traceN hStep hTrace hInit) hAbs

end AbstractInterpretation

end FormalMethods

end LeanMathlib
