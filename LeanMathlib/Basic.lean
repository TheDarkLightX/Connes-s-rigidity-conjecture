import Mathlib

namespace LeanMathlib

/--
Starter sanity theorem for the curated library.
This is intentionally simple: the goal is to keep a replayable, known-good
mathlib root ready before adding domain-specific proofs.
-/
theorem add_comm_curated (a b : Nat) : a + b = b + a := by
  simpa using Nat.add_comm a b

/-- Small arithmetic lemma that exercises a mathlib tactic surface. -/
theorem square_nonneg (x : Int) : 0 <= x ^ 2 := by
  nlinarith

end LeanMathlib
