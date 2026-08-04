import LeanMathlib.DeFi.RiskPolicy
import LeanMathlib.Order.BooleanSubalgebraMapWitness
import Mathlib.Order.BooleanSubalgebra

namespace LeanMathlib

open scoped symmDiff

/--
Observable boolean flags for the replayable lending-risk policy.

These are the protocol-facing booleans that feed `lendingRiskDecision`. We
package them as a finite Boolean cube so the order-theory library can certify
disagreement witnesses on the observable alarm surface itself.
-/
inductive RiskSignalTag
  | exploitWitness
  | oracleDivergence
  | solvencyGap
  | liquidationCascade
  | governanceOverride
  | healthy
  deriving DecidableEq, Fintype, Repr

/-- The Boolean cube of protocol-visible risk signals. -/
abbrev RiskSignalCube := RiskSignalTag → Bool

/-- Set-valued observable surface of active risk flags. -/
def activeFlagSet (signals : RiskSignalCube) : Set RiskSignalTag :=
  { flag | signals flag = true }

@[simp] theorem mem_activeFlagSet (signals : RiskSignalCube) (flag : RiskSignalTag) :
    flag ∈ activeFlagSet signals ↔ signals flag = true := Iff.rfl

/-- Replayable bridge from the Boolean cube to the powerset of active flags. -/
def activeFlagSetHom : BoundedLatticeHom RiskSignalCube (Set RiskSignalTag) where
  toFun := activeFlagSet
  map_sup' := by
    intro x y
    ext flag
    cases hx : x flag <;> cases hy : y flag <;> simp [activeFlagSet, hx, hy]
  map_inf' := by
    intro x y
    ext flag
    cases hx : x flag <;> cases hy : y flag <;> simp [activeFlagSet, hx, hy]
  map_top' := by
    ext flag
    simp [activeFlagSet]
  map_bot' := by
    ext flag
    simp [activeFlagSet]

theorem activeFlagSetHom_injective : Function.Injective activeFlagSetHom := by
  intro x y hxy
  funext flag
  have hmem := congrArg (fun s : Set RiskSignalTag => flag ∈ s) hxy
  cases hx : x flag <;> cases hy : y flag
  · rfl
  · exfalso
    have hmemY : flag ∈ activeFlagSet y := by
      simp [activeFlagSet, hy]
    have hmemX : flag ∈ activeFlagSet x := by
      change flag ∈ activeFlagSetHom x
      rw [hxy]
      exact hmemY
    simp [activeFlagSet, hx] at hmemX
  · exfalso
    have hmemX : flag ∈ activeFlagSet x := by
      simp [activeFlagSet, hx]
    have hmemY : flag ∈ activeFlagSet y := by
      change flag ∈ activeFlagSetHom y
      rw [← hxy]
      exact hmemX
    simp [activeFlagSet, hy] at hmemY
  · rfl

theorem activeFlagSetHom_surjective : Function.Surjective activeFlagSetHom := by
  classical
  intro s
  refine ⟨fun flag => decide (flag ∈ s), ?_⟩
  ext flag
  change (decide (flag ∈ s) = true) ↔ flag ∈ s
  by_cases hflag : flag ∈ s <;> simp [hflag]

/-- Order isomorphism between protocol risk cubes and the observable active-flag set surface. -/
noncomputable def activeFlagSetOrderIso : RiskSignalCube ≃o Set RiskSignalTag where
  toEquiv := Equiv.ofBijective activeFlagSet
    ⟨activeFlagSetHom_injective, activeFlagSetHom_surjective⟩
  map_rel_iff' := by
    intro x y
    exact
      (BooleanSubalgebra.le_iff_of_injective (f := activeFlagSetHom)
        activeFlagSetHom_injective (a := x) (b := y))

noncomputable instance : IsAtomic RiskSignalCube := by
  exact (OrderIso.isAtomic_iff activeFlagSetOrderIso).2 inferInstance

noncomputable instance : IsCoatomic RiskSignalCube := by
  exact (OrderIso.isCoatomic_iff activeFlagSetOrderIso).2 inferInstance

@[simp] theorem activeFlagSetOrderIso_apply (signals : RiskSignalCube) :
    activeFlagSetOrderIso signals = activeFlagSet signals := rfl

/-- The risk-policy action induced by a Boolean profile. -/
def riskSignalDecision (signals : RiskSignalCube) : LendingRiskAction :=
  lendingRiskDecision
    (signals .exploitWitness)
    (signals .oracleDivergence)
    (signals .solvencyGap)
    (signals .liquidationCascade)
    (signals .governanceOverride)
    (signals .healthy)

@[simp] theorem riskSignalDecision_eq (signals : RiskSignalCube) :
    riskSignalDecision signals =
      lendingRiskDecision
        (signals .exploitWitness)
        (signals .oracleDivergence)
        (signals .solvencyGap)
        (signals .liquidationCascade)
        (signals .governanceOverride)
        (signals .healthy) := rfl

theorem riskSignal_eq_iff_activeFlagSet_eq {x y : RiskSignalCube} :
    x = y ↔ activeFlagSet x = activeFlagSet y := by
  constructor
  · intro hxy
    simp [hxy]
  · intro hxy
    exact activeFlagSetHom_injective hxy

theorem riskSignalDecision_eq_of_activeFlagSet_eq {x y : RiskSignalCube}
    (hxy : activeFlagSet x = activeFlagSet y) :
    riskSignalDecision x = riskSignalDecision y := by
  simp [riskSignal_eq_iff_activeFlagSet_eq.2 hxy]

theorem riskSignal_ne_iff_exists_atom_disjoint_bihimp (x y : RiskSignalCube) :
    x ≠ y ↔ ∃ p : Set RiskSignalTag, IsAtom p ∧ Disjoint p (activeFlagSet x ⇔ activeFlagSet y) := by
  constructor
  · intro hxy
    have hset : activeFlagSet x ≠ activeFlagSet y := by
      intro hsetEq
      exact hxy (riskSignal_eq_iff_activeFlagSet_eq.2 hsetEq)
    exact (ne_iff_exists_atom_disjoint_bihimp (a := activeFlagSet x) (b := activeFlagSet y)).1 hset
  · intro hxy
    have hset : activeFlagSet x ≠ activeFlagSet y :=
      (ne_iff_exists_atom_disjoint_bihimp (a := activeFlagSet x) (b := activeFlagSet y)).2 hxy
    intro hEq
    exact hset (riskSignal_eq_iff_activeFlagSet_eq.1 hEq)

theorem riskSignal_eq_iff_forall_atoms_not_disjoint_bihimp (x y : RiskSignalCube) :
    x = y ↔
      ∀ p : Set RiskSignalTag, IsAtom p → ¬ Disjoint p (activeFlagSet x ⇔ activeFlagSet y) := by
  constructor
  · intro hxy
    exact (eq_iff_forall_atom_not_disjoint_bihimp (a := activeFlagSet x) (b := activeFlagSet y)).1
      (riskSignal_eq_iff_activeFlagSet_eq.1 hxy)
  · intro hxy
    exact riskSignal_eq_iff_activeFlagSet_eq.2 <|
      (eq_iff_forall_atom_not_disjoint_bihimp (a := activeFlagSet x) (b := activeFlagSet y)).2 hxy

theorem riskSignal_ne_iff_exists_flag_disjoint_bihimp (x y : RiskSignalCube) :
    x ≠ y ↔
      ∃ flag : RiskSignalTag,
        Disjoint ({flag} : Set RiskSignalTag) (activeFlagSet x ⇔ activeFlagSet y) := by
  constructor
  · intro hxy
    rcases (riskSignal_ne_iff_exists_atom_disjoint_bihimp x y).1 hxy with ⟨p, hp, hpd⟩
    rcases Set.isAtom_iff.1 hp with ⟨flag, rfl⟩
    exact ⟨flag, hpd⟩
  · rintro ⟨flag, hpd⟩
    exact (riskSignal_ne_iff_exists_atom_disjoint_bihimp x y).2
      ⟨{flag}, Set.isAtom_singleton flag, hpd⟩

theorem riskSignal_ne_iff_exists_flag_in_symmDiff (x y : RiskSignalCube) :
    x ≠ y ↔
      ∃ flag : RiskSignalTag, flag ∈ activeFlagSet x ∆ activeFlagSet y := by
  rw [riskSignal_ne_iff_exists_flag_disjoint_bihimp]
  constructor
  · rintro ⟨flag, hdisj⟩
    have hsubset : ({flag} : Set RiskSignalTag) ≤ activeFlagSet x ∆ activeFlagSet y :=
      (le_symmDiff_iff_disjoint_bihimp (a := activeFlagSet x) (b := activeFlagSet y)
        (p := {flag})).2 hdisj
    exact ⟨flag, hsubset (by simp)⟩
  · rintro ⟨flag, hflag⟩
    refine ⟨flag, ?_⟩
    have hsubset : ({flag} : Set RiskSignalTag) ≤ activeFlagSet x ∆ activeFlagSet y := by
      intro a ha
      simpa [Set.mem_singleton_iff.mp ha] using hflag
    exact (le_symmDiff_iff_disjoint_bihimp (a := activeFlagSet x) (b := activeFlagSet y)
      (p := {flag})).1 hsubset

theorem exists_flag_witness_of_riskSignalDecision_ne {x y : RiskSignalCube}
    (hxy : riskSignalDecision x ≠ riskSignalDecision y) :
    ∃ flag : RiskSignalTag, flag ∈ activeFlagSet x ∆ activeFlagSet y := by
  have hneq : x ≠ y := by
    intro hEq
    exact hxy (hEq ▸ rfl)
  exact (riskSignal_ne_iff_exists_flag_in_symmDiff x y).1 hneq

theorem riskSignalDecision_eq_allow_iff_activeFlagSet_eq_healthy (signals : RiskSignalCube) :
    riskSignalDecision signals = .allow ↔
      activeFlagSet signals = ({RiskSignalTag.healthy} : Set RiskSignalTag) := by
  constructor
  · intro hAllow
    ext flag
    cases flag <;>
      simp [activeFlagSet,
        (lendingRiskDecision_eq_allow_iff
          (signals .exploitWitness)
          (signals .oracleDivergence)
          (signals .solvencyGap)
          (signals .liquidationCascade)
          (signals .governanceOverride)
          (signals .healthy)).1 hAllow]
  · intro hSet
    have hExploit : signals .exploitWitness = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.exploitWitness ∈ s) hSet
      simpa [activeFlagSet] using this
    have hOracle : signals .oracleDivergence = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.oracleDivergence ∈ s) hSet
      simpa [activeFlagSet] using this
    have hSolvency : signals .solvencyGap = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.solvencyGap ∈ s) hSet
      simpa [activeFlagSet] using this
    have hCascade : signals .liquidationCascade = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.liquidationCascade ∈ s) hSet
      simpa [activeFlagSet] using this
    have hGovernance : signals .governanceOverride = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.governanceOverride ∈ s) hSet
      simpa [activeFlagSet] using this
    have hHealthy : signals .healthy = true := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.healthy ∈ s) hSet
      simpa [activeFlagSet] using this
    exact (lendingRiskDecision_eq_allow_iff
      (signals .exploitWitness)
      (signals .oracleDivergence)
      (signals .solvencyGap)
      (signals .liquidationCascade)
      (signals .governanceOverride)
      (signals .healthy)).2
        ⟨hExploit, hOracle, hSolvency, hCascade, hGovernance, hHealthy⟩

theorem riskSignalDecision_eq_deny_iff_activeFlagSet_eq_empty (signals : RiskSignalCube) :
    riskSignalDecision signals = .deny ↔
      activeFlagSet signals = (∅ : Set RiskSignalTag) := by
  constructor
  · intro hDeny
    ext flag
    cases flag <;>
      simp [activeFlagSet,
        (lendingRiskDecision_eq_deny_iff
          (signals .exploitWitness)
          (signals .oracleDivergence)
          (signals .solvencyGap)
          (signals .liquidationCascade)
          (signals .governanceOverride)
          (signals .healthy)).1 hDeny]
  · intro hSet
    have hExploit : signals .exploitWitness = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.exploitWitness ∈ s) hSet
      simpa [activeFlagSet] using this
    have hOracle : signals .oracleDivergence = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.oracleDivergence ∈ s) hSet
      simpa [activeFlagSet] using this
    have hSolvency : signals .solvencyGap = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.solvencyGap ∈ s) hSet
      simpa [activeFlagSet] using this
    have hCascade : signals .liquidationCascade = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.liquidationCascade ∈ s) hSet
      simpa [activeFlagSet] using this
    have hGovernance : signals .governanceOverride = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.governanceOverride ∈ s) hSet
      simpa [activeFlagSet] using this
    have hHealthy : signals .healthy = false := by
      have := congrArg (fun s : Set RiskSignalTag => RiskSignalTag.healthy ∈ s) hSet
      simpa [activeFlagSet] using this
    exact (lendingRiskDecision_eq_deny_iff
      (signals .exploitWitness)
      (signals .oracleDivergence)
      (signals .solvencyGap)
      (signals .liquidationCascade)
      (signals .governanceOverride)
      (signals .healthy)).2
        ⟨hExploit, hOracle, hSolvency, hCascade, hGovernance, hHealthy⟩

end LeanMathlib
