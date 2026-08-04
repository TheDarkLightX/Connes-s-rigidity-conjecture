import Mathlib
import LeanMathlib.DeFi.BorrowCoreV0Bridge

namespace LeanMathlib

/-- Stability-pool collateral cap aligned to the local `borrow_core_v0.py` core. -/
def borrowCoreV0MaxSpColl : Rat := 40

/-- Total system collateral, including the stability pool. -/
def systemCollateral (state : SimplexBorrowState) : Rat :=
  state.troveA.collateral + state.troveB.collateral + state.spColl

/-- Total outstanding trove debt. -/
def systemTroveDebt (state : SimplexBorrowState) : Rat :=
  state.troveA.debt + state.troveB.debt

/-- System-wide collateral value at a given price. -/
def systemCollateralValue (state : SimplexBorrowState) (price : Rat) : Rat :=
  systemCollateral state * price

/-- A single trove has no bad debt when its collateral value covers its debt. -/
def troveNoBadDebt (trove : SimplexTrove) (price : Rat) : Prop :=
  trove.debt ≤ trove.collateral * price

/-- System-wide debt is covered by troves plus the stability pool. -/
def systemNoBadDebt (state : SimplexBorrowState) (price : Rat) : Prop :=
  systemTroveDebt state ≤ systemCollateralValue state price

/-- `deposit_sp` transition from the local functional core. -/
def depositSP (state : SimplexBorrowState) (amt : Rat) : SimplexBorrowState :=
  { state with
    freeDebt := state.freeDebt - amt
    spDebt := state.spDebt + amt }

/-- `withdraw_sp` transition from the local functional core. -/
def withdrawSP (state : SimplexBorrowState) (amt : Rat) : SimplexBorrowState :=
  { state with
    spDebt := state.spDebt - amt
    freeDebt := state.freeDebt + amt }

/-- `liquidate_a` transition from the local functional core. -/
def liquidateA (state : SimplexBorrowState) : SimplexBorrowState :=
  { state with
    spDebt := state.spDebt - state.troveA.debt
    spColl := state.spColl + state.troveA.collateral
    troveA := { collateral := 0, debt := 0 } }

/-- Guard for `deposit_sp`. -/
def depositSPGuard
    (state : SimplexBorrowState)
    (amt : Rat) : Prop :=
  0 < amt ∧
    amt ≤ state.freeDebt ∧
    state.spDebt + amt ≤ borrowCoreV0Params.maxDebtSupply

/-- Guard for `withdraw_sp`. -/
def withdrawSPGuard
    (state : SimplexBorrowState)
    (amt : Rat) : Prop :=
  0 < amt ∧
    amt ≤ state.spDebt ∧
    state.freeDebt + amt ≤ borrowCoreV0Params.maxDebtSupply ∧
    mcrOkAtQuotedPrice borrowCoreV0Params state.troveA ∧
    mcrOkAtQuotedPrice borrowCoreV0Params state.troveB

/-- Guard for `liquidate_a`. -/
def liquidateAGuard (state : SimplexBorrowState) : Prop :=
  0 < state.troveA.debt ∧
    ¬ mcrOkAtQuotedPrice borrowCoreV0Params state.troveA ∧
    state.troveA.debt ≤ state.spDebt ∧
    state.spColl + state.troveA.collateral ≤ borrowCoreV0MaxSpColl

theorem systemNoBadDebt_of_trovesNoBadDebt
    (state : SimplexBorrowState)
    {price : Rat}
    (hA : troveNoBadDebt state.troveA price)
    (hB : troveNoBadDebt state.troveB price)
    (hSp : 0 ≤ state.spColl)
    (hPrice : 0 ≤ price) :
    systemNoBadDebt state price := by
  dsimp [troveNoBadDebt, systemNoBadDebt, systemTroveDebt, systemCollateralValue,
    systemCollateral] at *
  have hSpValue : 0 ≤ state.spColl * price := mul_nonneg hSp hPrice
  nlinarith

theorem depositSP_preserves_supplyConservation
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSupply : supplyConservation state) :
    supplyConservation (depositSP state amt) := by
  dsimp [supplyConservation, depositSP] at *
  linarith

theorem withdrawSP_preserves_supplyConservation
    (state : SimplexBorrowState)
    (amt : Rat)
    (hSupply : supplyConservation state) :
    supplyConservation (withdrawSP state amt) := by
  dsimp [supplyConservation, withdrawSP] at *
  linarith

theorem liquidateA_preserves_supplyConservation
    (state : SimplexBorrowState)
    (hSupply : supplyConservation state) :
    supplyConservation (liquidateA state) := by
  dsimp [supplyConservation, liquidateA] at *
  linarith

theorem depositSP_preserves_systemNoBadDebt
    (state : SimplexBorrowState)
    {price : Rat}
    (amt : Rat)
    (hSystem : systemNoBadDebt state price) :
    systemNoBadDebt (depositSP state amt) price := by
  simpa [systemNoBadDebt, systemTroveDebt, systemCollateralValue, systemCollateral, depositSP]
    using hSystem

theorem withdrawSP_preserves_systemNoBadDebt
    (state : SimplexBorrowState)
    {price : Rat}
    (amt : Rat)
    (hSystem : systemNoBadDebt state price) :
    systemNoBadDebt (withdrawSP state amt) price := by
  simpa [systemNoBadDebt, systemTroveDebt, systemCollateralValue, systemCollateral, withdrawSP]
    using hSystem

theorem liquidateA_systemCollateralValue_eq
    (state : SimplexBorrowState)
    (price : Rat) :
    systemCollateralValue (liquidateA state) price =
      systemCollateralValue state price := by
  dsimp [systemCollateralValue, systemCollateral, liquidateA]
  ring

theorem liquidateA_preserves_systemNoBadDebt
    (state : SimplexBorrowState)
    {price : Rat}
    (hDebtNonneg : 0 ≤ state.troveA.debt)
    (hSystem : systemNoBadDebt state price) :
    systemNoBadDebt (liquidateA state) price := by
  have hDebt :
      systemTroveDebt (liquidateA state) ≤ systemTroveDebt state := by
    dsimp [systemTroveDebt, liquidateA]
    linarith
  calc
    systemTroveDebt (liquidateA state)
      ≤ systemTroveDebt state := hDebt
    _ ≤ systemCollateralValue state price := hSystem
    _ = systemCollateralValue (liquidateA state) price := by
      symm
      exact liquidateA_systemCollateralValue_eq state price

theorem withdrawSPGuard_implies_troveA_solventAt_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : withdrawSPGuard state amt) :
    solventAt (trovePosition borrowCoreV0Params state.troveA)
      borrowCoreV0Params.priceCents := by
  exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
    borrowCoreV0Params
    state.troveA
    borrowCoreV0Params_mcrDen_pos).2 hGuard.2.2.2.1

theorem withdrawSPGuard_implies_troveB_solventAt_quoted
    (state : SimplexBorrowState)
    (amt : Rat)
    (hGuard : withdrawSPGuard state amt) :
    solventAt (trovePosition borrowCoreV0Params state.troveB)
      borrowCoreV0Params.priceCents := by
  exact (solventAt_quoted_iff_mcrOkAtQuotedPrice
    borrowCoreV0Params
    state.troveB
    borrowCoreV0Params_mcrDen_pos).2 hGuard.2.2.2.2

theorem liquidateAGuard_implies_not_solventAt_quoted
    (state : SimplexBorrowState)
    (hGuard : liquidateAGuard state) :
    ¬ solventAt (trovePosition borrowCoreV0Params state.troveA)
        borrowCoreV0Params.priceCents := by
  intro hSolvent
  exact hGuard.2.1 <|
    (solventAt_quoted_iff_mcrOkAtQuotedPrice
      borrowCoreV0Params
      state.troveA
      borrowCoreV0Params_mcrDen_pos).1 hSolvent

theorem liquidateA_offsets_sp_debt
    (state : SimplexBorrowState) :
    (liquidateA state).spDebt = state.spDebt - state.troveA.debt := by
  rfl

theorem liquidateA_moves_collateral_to_sp
    (state : SimplexBorrowState) :
    (liquidateA state).spColl = state.spColl + state.troveA.collateral := by
  rfl

theorem liquidateA_clears_troveA
    (state : SimplexBorrowState) :
    (liquidateA state).troveA = ({ collateral := 0, debt := 0 } : SimplexTrove) := by
  rfl

end LeanMathlib
