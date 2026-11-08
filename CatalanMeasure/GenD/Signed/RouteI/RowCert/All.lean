module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RowP0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RowP1
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RowN0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RowN1
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.Hdata

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The moved free rows of `capSource` (ledger G30): the caps `c0R` and `c1R`

For the design C anchor move `(da0, dv0)` and `(da1, dv1)` (the integer lists of `Hdata` over `2^40`), the free row at anchor 0 plus the move
`h = -2 T(da0 + tau da1) - S(dv0 + tau dv1)` is at most `c0R` for `tau = 0` and at most `c1R` for `tau = 1`, on all of `rowDom`.
The statements have the shape `chord_row` and `selected_comparison` consume (`freeRow + fRm ... tau x <= c`).

kcost: no computation here.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set
open OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.RouteI.RowCertMoved

noncomputable def movA0 : ℕ → ℝ := movSeq aL0 DH
noncomputable def movA1 : ℕ → ℝ := movSeq aL1 DH
noncomputable def movV0 : ℕ → ℝ := movSeq vL0 DH
noncomputable def movV1 : ℕ → ℝ := movSeq vL1 DH

theorem getD_addZ' : ∀ (a b : List ℤ) (i : ℕ), (addZ a b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], b, i => by simp [addZ]
  | a :: t, [], i => by simp [addZ]
  | a :: t, b :: r, 0 => by simp [addZ]
  | a :: t, b :: r, i + 1 => by simpa [addZ] using getD_addZ' t r i

theorem movSeq_addZ (a b : List ℤ) (D : ℕ) (k : ℕ) : movSeq a D k + movSeq b D k = movSeq (addZ a b) D k := by
  unfold movSeq
  split_ifs
  · simp
  · rw [getD_addZ']; push_cast; ring

theorem hMov0_eq (x : ℝ) : hMov0 x = -(2 * barrierTrialT (fun k => movA0 k + (0 : ℝ) * movA1 k) x) -
    barrierTrialS (fun k => movV0 k + (0 : ℝ) * movV1 k) x := by
  have e1 : (fun k => movA0 k + (0 : ℝ) * movA1 k) = movSeq aL0 DH := by funext k; simp [movA0]
  have e2 : (fun k => movV0 k + (0 : ℝ) * movV1 k) = movSeq vL0 DH := by funext k; simp [movV0]
  rw [e1, e2, barrierTrialT_movSeq, barrierTrialS_movSeq]
  unfold hMov0 wT0 wS0
  rw [refT_smul, refS_smul]
  push_cast
  ring

theorem hMov1_eq (x : ℝ) : hMov1 x = -(2 * barrierTrialT (fun k => movA0 k + (1 : ℝ) * movA1 k) x) -
    barrierTrialS (fun k => movV0 k + (1 : ℝ) * movV1 k) x := by
  have e1 : (fun k => movA0 k + (1 : ℝ) * movA1 k) = movSeq (addZ aL0 aL1) DH := by
    funext k; rw [← movSeq_addZ]; simp [movA0, movA1]
  have e2 : (fun k => movV0 k + (1 : ℝ) * movV1 k) = movSeq (addZ vL0 vL1) DH := by
    funext k; rw [← movSeq_addZ]; simp [movV0, movV1]
  rw [e1, e2, barrierTrialT_movSeq, barrierTrialS_movSeq]
  unfold hMov1 wT1 wS1
  rw [refT_smul, refS_smul]
  push_cast
  ring

/-- **(R0)** the moved free row at `tau = 0`. -/
theorem c0R_cert : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x +
    (-(2 * barrierTrialT (fun k => movA0 k + (0 : ℝ) * movA1 k) x) -
      barrierTrialS (fun k => movV0 k + (0 : ℝ) * movV1 k) x) ≤ ((-2579740254 / 1000000000 : ℚ) : ℝ) := by
  intro x hx
  have h := movedRowCap_of_checks hMov0 rowP0 rowN0 x hx
  rw [hMov0_eq] at h
  have e : ((-2579740254 / 1000000000 : ℚ) : ℝ) = (-2579740254 / 1000000000 : ℝ) := by norm_num
  rw [e]
  exact h

/-- **(R1)** the moved free row at `tau = 1`. -/
theorem c1R_cert : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x +
    (-(2 * barrierTrialT (fun k => movA0 k + (1 : ℝ) * movA1 k) x) -
      barrierTrialS (fun k => movV0 k + (1 : ℝ) * movV1 k) x) ≤ ((-2574009165 / 1000000000 : ℚ) : ℝ) := by
  intro x hx
  have h := movedRowCap_of_checks hMov1 rowP1 rowN1 x hx
  rw [hMov1_eq] at h
  have e : ((-2574009165 / 1000000000 : ℚ) : ℝ) = (-2574009165 / 1000000000 : ℝ) := by norm_num
  rw [e]
  exact h

end CatalanMeasure.GenD.Signed.RouteI.RowCert
