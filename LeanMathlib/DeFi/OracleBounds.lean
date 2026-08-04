import Mathlib

namespace LeanMathlib

/-!
Minimal oracle-bound lending algebra for the curated DeFi library.

This module uses exact rationals to avoid premature discretization while keeping
the proof surface small and deterministic.
-/

/--
`OracleBounds` packages a quoted price together with a maximum downward
deviation used in worst-case solvency arguments.
-/
structure OracleBounds where
  quotedPrice : Rat
  maxDownwardDeviation : Rat

/-- Worst-case price induced by a bounded downward oracle deviation. -/
def adversePrice (bounds : OracleBounds) : Rat :=
  bounds.quotedPrice - bounds.maxDownwardDeviation

/--
An actual price lies in the oracle envelope when it stays between the adverse
lower bound and the quoted price.
-/
def inOracleEnvelope (bounds : OracleBounds) (actualPrice : Rat) : Prop :=
  adversePrice bounds ≤ actualPrice ∧ actualPrice ≤ bounds.quotedPrice

/--
Minimal lending state for solvency reasoning.

`liquidationThreshold * debt` is the required value floor, and
`collateral * price` is the current collateral value.
-/
structure LendingPosition where
  collateral : Rat
  debt : Rat
  liquidationThreshold : Rat

/-- Current collateral value at a given price. -/
def collateralValue (position : LendingPosition) (price : Rat) : Rat :=
  position.collateral * price

/--
Signed solvency slack. Nonnegative margin means the position is solvent at the
chosen price.
-/
def solvencyMargin (position : LendingPosition) (price : Rat) : Rat :=
  collateralValue position price - position.liquidationThreshold * position.debt

/-- Basic solvency predicate at a given price. -/
def solventAt (position : LendingPosition) (price : Rat) : Prop :=
  position.liquidationThreshold * position.debt ≤ collateralValue position price

theorem adversePrice_le_quotedPrice
    (bounds : OracleBounds)
    (hDeviation : 0 ≤ bounds.maxDownwardDeviation) :
    adversePrice bounds ≤ bounds.quotedPrice := by
  simpa [adversePrice] using sub_le_self bounds.quotedPrice hDeviation

theorem adversePrice_nonneg
    (bounds : OracleBounds)
    (hBound : bounds.maxDownwardDeviation ≤ bounds.quotedPrice) :
    0 ≤ adversePrice bounds := by
  dsimp [adversePrice]
  exact sub_nonneg.mpr hBound

theorem quotedPrice_mem_oracleEnvelope
    (bounds : OracleBounds)
    (hDeviation : 0 ≤ bounds.maxDownwardDeviation) :
    inOracleEnvelope bounds bounds.quotedPrice := by
  exact ⟨adversePrice_le_quotedPrice bounds hDeviation, le_rfl⟩

theorem collateralValue_nonneg
    (position : LendingPosition)
    {price : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hPrice : 0 ≤ price) :
    0 ≤ collateralValue position price := by
  dsimp [collateralValue]
  exact mul_nonneg hCollateral hPrice

theorem collateralValue_mono
    (position : LendingPosition)
    {price₁ price₂ : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hPrice : price₁ ≤ price₂) :
    collateralValue position price₁ ≤ collateralValue position price₂ := by
  dsimp [collateralValue]
  exact mul_le_mul_of_nonneg_left hPrice hCollateral

theorem solvencyMargin_mono
    (position : LendingPosition)
    {price₁ price₂ : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hPrice : price₁ ≤ price₂) :
    solvencyMargin position price₁ ≤ solvencyMargin position price₂ := by
  dsimp [solvencyMargin]
  exact sub_le_sub_right
    (collateralValue_mono position hCollateral hPrice)
    (position.liquidationThreshold * position.debt)

theorem solventAt_iff_nonneg_solvencyMargin
    (position : LendingPosition)
    (price : Rat) :
    solventAt position price ↔ 0 ≤ solvencyMargin position price := by
  constructor
  · intro hSolvent
    dsimp [solventAt, solvencyMargin, collateralValue] at *
    exact sub_nonneg.mpr hSolvent
  · intro hMargin
    dsimp [solvencyMargin, solventAt, collateralValue] at *
    exact sub_nonneg.mp hMargin

theorem solventAt_mono
    (position : LendingPosition)
    {price₁ price₂ : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hPrice : price₁ ≤ price₂)
    (hSolvent : solventAt position price₁) :
    solventAt position price₂ := by
  rw [solventAt_iff_nonneg_solvencyMargin] at hSolvent ⊢
  exact le_trans hSolvent (solvencyMargin_mono position hCollateral hPrice)

theorem solventAt_of_adversePriceLowerBound
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hLower : adversePrice bounds ≤ actualPrice)
    (hSolvent : solventAt position (adversePrice bounds)) :
    solventAt position actualPrice := by
  exact solventAt_mono position hCollateral hLower hSolvent

theorem solventAt_of_inOracleEnvelope
    (position : LendingPosition)
    (bounds : OracleBounds)
    {actualPrice : Rat}
    (hCollateral : 0 ≤ position.collateral)
    (hEnvelope : inOracleEnvelope bounds actualPrice)
    (hSolvent : solventAt position (adversePrice bounds)) :
    solventAt position actualPrice := by
  exact solventAt_of_adversePriceLowerBound position bounds
    hCollateral hEnvelope.1 hSolvent

theorem solventAt_quotedPrice_of_solventAt_adverse
    (position : LendingPosition)
    (bounds : OracleBounds)
    (hCollateral : 0 ≤ position.collateral)
    (hDeviation : 0 ≤ bounds.maxDownwardDeviation)
    (hSolvent : solventAt position (adversePrice bounds)) :
    solventAt position bounds.quotedPrice := by
  exact solventAt_of_adversePriceLowerBound position bounds hCollateral
    (adversePrice_le_quotedPrice bounds hDeviation) hSolvent

end LeanMathlib
