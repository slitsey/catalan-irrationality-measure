module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedCaps
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedLitsEq
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU00
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU01
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU02
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU03
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU04
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU05
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU06
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU07
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU08
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU09
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU10
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU11
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedU12
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.All

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Moved column caps (G31): the certified caps C0, C1, C2

`movedC0`, `movedC1`, `movedC2` are the caps `c0C`, `c1C`, `c2C` consumed by `chord_col`/`chord_col_gamma`
(`TerminalC`: hypotheses `C0`, `C1`, `C2`), for the design-C anchor-move list `dv0, dv1` (`TrialC`, over `2^40`) and
`g(s) = log (1 + (3/4) s)`:

* `movedC0`: `F_C(s) + 2 T(dv0, s) ≤ c0C`,
* `movedC1`: `F_C(s) + 2 T(dv0 + dv1, s) + (1/25) g(s) ≤ c1C`,
* `movedC2`: `F_C(s) + 2 T(dv0 + dv1, s) + (51/500) g(s) ≤ c2C`,

on `0 < s < 1`, with `F_C = capSource.colField 0`.  The units are those of `ColCert.All` (the anchor-0 free column,
unchanged by the anchor move); each unit carries the exact moved polynomials (`finMv`).

kcost: assembly only, below 1 s estimated.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved

open Set CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCert
open CatalanMeasure.GenD.Signed.RouteI.RowCertMoved (movSeq)
open OAI.InternalCatalan

theorem Lall_mv : ∀ u ∈ All.Lall, finMv u m0 m1 cap0n cap1n cap2n = true :=
  List.forall_mem_append.2 ⟨L0_mv, List.forall_mem_append.2 ⟨L1_mv, List.forall_mem_append.2 ⟨L2_mv, List.forall_mem_append.2 ⟨L3_mv, List.forall_mem_append.2 ⟨L4_mv, List.forall_mem_append.2 ⟨L5_mv, List.forall_mem_append.2 ⟨L6_mv, List.forall_mem_append.2 ⟨L7_mv, List.forall_mem_append.2 ⟨L8_mv, List.forall_mem_append.2 ⟨L9_mv, List.forall_mem_append.2 ⟨L10_mv, List.forall_mem_append.2 ⟨L11_mv, L12_mv⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem c0Cq_eq : ((c0Cq : ℚ) : ℝ) = (cap0n : ℝ) / 10 ^ 9 := by unfold c0Cq; push_cast; ring
theorem c1Cq_eq : ((c1Cq : ℚ) : ℝ) = (cap1n : ℝ) / 10 ^ 9 := by unfold c1Cq; push_cast; ring
theorem c2Cq_eq : ((c2Cq : ℚ) : ℝ) = (cap2n : ℝ) / 10 ^ 9 := by unfold c2Cq; push_cast; ring

theorem movedC0 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s +
    2 * barrierTrialT (movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv0
      CatalanMeasure.GenD.Signed.RouteI.TrialC.D) s ≤ ((c0Cq : ℚ) : ℝ) := by
  have h := moved_of_units (fun s => 2 * barrierTrialT (movSeq m0.ws m0.D) s) ((cap0n : ℝ) / 10 ^ 9) V0 V385
    All.Lall 2258509194 999987067382
    (cap0_of_fin V0 (UnitV'_of_V V0_V) m0 m1 b0_eq V0_mv)
    (cap0_of_fin V385 (UnitV'_of_V V385_V) m0 m1 b0_eq V385_mv)
    (fun u hu => cap0_of_fin u (UnitV'_of_V (All.Lall_V u hu)) m0 m1 b0_eq (Lall_mv u hu))
    All.chain_true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs
  rw [c0Cq_eq]
  exact h s hs

theorem movedC1 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s +
    2 * barrierTrialT (movSeq ws1 CatalanMeasure.GenD.Signed.RouteI.TrialC.D) s +
      (1 / 25 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ ((c1Cq : ℚ) : ℝ) := by
  have h := moved_of_units
    (fun s => 2 * barrierTrialT (movSeq m1.ws m1.D) s + (1 / 25 : ℝ) * Real.log (1 + 3 / 4 * s))
    ((cap1n : ℝ) / 10 ^ 9) V0 V385 All.Lall 2258509194 999987067382
    (cap1_of_fin V0 (UnitV'_of_V V0_V) m0 m1 b1_eq V0_mv)
    (cap1_of_fin V385 (UnitV'_of_V V385_V) m0 m1 b1_eq V385_mv)
    (fun u hu => cap1_of_fin u (UnitV'_of_V (All.Lall_V u hu)) m0 m1 b1_eq (Lall_mv u hu))
    All.chain_true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs
  rw [c1Cq_eq]
  have := h s hs
  rw [add_assoc]
  exact this

theorem movedC2 : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s +
    2 * barrierTrialT (movSeq ws1 CatalanMeasure.GenD.Signed.RouteI.TrialC.D) s +
      (51 / 500 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ ((c2Cq : ℚ) : ℝ) := by
  have h := moved_of_units
    (fun s => 2 * barrierTrialT (movSeq m1.ws m1.D) s + (51 / 500 : ℝ) * Real.log (1 + 3 / 4 * s))
    ((cap2n : ℝ) / 10 ^ 9) V0 V385 All.Lall 2258509194 999987067382
    (cap2_of_fin V0 (UnitV'_of_V V0_V) m0 m1 b1_eq V0_mv)
    (cap2_of_fin V385 (UnitV'_of_V V385_V) m0 m1 b1_eq V385_mv)
    (fun u hu => cap2_of_fin u (UnitV'_of_V (All.Lall_V u hu)) m0 m1 b1_eq (Lall_mv u hu))
    All.chain_true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs
  rw [c2Cq_eq]
  have := h s hs
  rw [add_assoc]
  exact this

theorem movSeq_addL (l0 l1 : List ℤ) (D : ℕ) (k : ℕ) :
    movSeq (addL l0 l1) D k = movSeq l0 D k + movSeq l1 D k := by
  unfold movSeq
  split_ifs with h
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    have := addL_get l0 l1 (k - 1)
    simp only [List.getD_eq_getElem?_getD] at this
    rw [this]; push_cast; ring

/-- `C1` in the shape of `TerminalC` (`fCm dv0 dv1 1 s = 2 * barrierTrialT (fun k => dv0 k + 1 * dv1 k) s`). -/
theorem movedC1' (dv0 dv1 : ℕ → ℝ) (h0 : dv0 = movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv0
      CatalanMeasure.GenD.Signed.RouteI.TrialC.D)
    (h1 : dv1 = movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv1 CatalanMeasure.GenD.Signed.RouteI.TrialC.D) :
    ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + 2 * barrierTrialT (fun k => dv0 k + 1 * dv1 k) s +
      (1 / 25 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ ((c1Cq : ℚ) : ℝ) := by
  have e : (fun k => dv0 k + 1 * dv1 k) = movSeq ws1 CatalanMeasure.GenD.Signed.RouteI.TrialC.D := by
    funext k; subst h0 h1; rw [one_mul]; exact (movSeq_addL _ _ _ k).symm
  rw [e]; exact movedC1

theorem movedC2' (dv0 dv1 : ℕ → ℝ) (h0 : dv0 = movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv0
      CatalanMeasure.GenD.Signed.RouteI.TrialC.D)
    (h1 : dv1 = movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv1 CatalanMeasure.GenD.Signed.RouteI.TrialC.D) :
    ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + 2 * barrierTrialT (fun k => dv0 k + 1 * dv1 k) s +
      (51 / 500 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ ((c2Cq : ℚ) : ℝ) := by
  have e : (fun k => dv0 k + 1 * dv1 k) = movSeq ws1 CatalanMeasure.GenD.Signed.RouteI.TrialC.D := by
    funext k; subst h0 h1; rw [one_mul]; exact (movSeq_addL _ _ _ k).symm
  rw [e]; exact movedC2

/-- `C0` in the shape of `TerminalC` (`fCm dv0 dv1 0 s = 2 * barrierTrialT (fun k => dv0 k + 0 * dv1 k) s`). -/
theorem movedC0' (dv0 dv1 : ℕ → ℝ) (h0 : dv0 = movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv0
      CatalanMeasure.GenD.Signed.RouteI.TrialC.D) :
    ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + 2 * barrierTrialT (fun k => dv0 k + 0 * dv1 k) s ≤
      ((c0Cq : ℚ) : ℝ) := by
  have e : (fun k => dv0 k + 0 * dv1 k) = movSeq CatalanMeasure.GenD.Signed.RouteI.TrialC.dv0
      CatalanMeasure.GenD.Signed.RouteI.TrialC.D := by
    funext k; subst h0; rw [zero_mul, add_zero]
  rw [e]; exact movedC0

#print axioms movedC0
#print axioms movedC1
#print axioms movedC2
#print axioms movedC0'
#print axioms movedC1'
#print axioms movedC2'

end CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved
