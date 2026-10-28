import CatalanCore.Uniform.Decay.NearFast.Cell
set_option Elab.async false

/-!
# The jet cell with a linear shift (lane D, package D15)

`cellOkFL` is `NearFast.cellOkF` with the Bernstein polynomial shifted by a linear form `α + β s`:
the rule certifies `m' ≤ -∑ w_P Φ_P(z) + cpi |Im z| + (α + β s)` for `z = zc + s dd + δ`.
With the negated pieces, `cpi = 0`, `m' = 0` this is an upper bound of `g` by the line `α + β s`
(the majorant of a piecewise-linear cap cell, `CapPL`).  The proof is that of `cellOkF_sound`
with `coeffs_addL` used once more.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearFast

theorem sum_coeffs_addL (a b : List ℚ) (n : ℕ) (s : ℝ) :
    ∑ m ∈ range n, ((coeffs (addL a b) m : ℚ) : ℝ) * s ^ m
      = ∑ m ∈ range n, ((coeffs a m : ℚ) : ℝ) * s ^ m + ∑ m ∈ range n, ((coeffs b m : ℚ) : ℝ) * s ^ m := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeffs_addL]; push_cast; ring

theorem sum_coeffs_lin (α β : ℚ) (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    ∑ m ∈ range n, ((coeffs [α, β] m : ℚ) : ℝ) * s ^ m = (α : ℝ) + β * s := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h3 : ∀ m ∈ range k, ((coeffs [α, β] (m + 1 + 1) : ℚ) : ℝ) * s ^ (m + 1 + 1) = 0 := by
    intro m _; simp [coeffs]
  rw [Finset.sum_eq_zero h3]
  simp [coeffs]; ring

/-- The cell rule with a linear shift `α + β s` of the Bernstein polynomial. -/
def cellOkFL (n : ℕ) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi lo m' : ℚ) (C : List ℚ) (Fs : ℚ)
    (eW eP : ℕ) (α β : ℚ) : Bool :=
  match aggEvalMF n zc dd h ps with
  | some (C0, F0) =>
    decide (0 < h) && decide (h ≤ 1) && decide (0 < W) && decide (0 ≤ cpi) && decide (2 ≤ n) &&
      decide (0 ≤ zc.im - h * |dd.im|) && decide (C0 = C) && decide (F0 ≤ Fs) &&
      bernLoOk2 (coeffs (addL (cellPoly C cpi zc dd) [α, β])) (n - 1) (-h) (2 * h) lo &&
      modAll Rtwo W eW eP ps &&
      decide (m' ≤ lo - Fs - modSum Rtwo W eW eP ps)
  | none => false

/-- **The cell rule with a linear shift.** -/
theorem cellOkFL_sound {n : ℕ} {ps : List WP} {zc dd : CQ} {h W Rtwo cpi lo m' : ℚ} {C : List ℚ}
    {Fs : ℚ} {eW eP : ℕ} {α β : ℚ}
    (hc : cellOkFL n ps zc dd h W Rtwo cpi lo m' C Fs eW eP α β = true) (s δ : ℝ) (hs : |s| ≤ h)
    (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| + ((α : ℝ) + β * s) := by
  unfold cellOkFL at hc
  split at hc
  · rename_i C0 F0 hag
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hh1⟩, hW⟩, hcpi⟩, hn2⟩, hy0⟩, hcl⟩, hF⟩, hbern⟩, hmod⟩, hfin⟩ := hc
    have hcl' := hcl.symm
    subst hcl'
    have hbern := bernLoOk2_imp hbern
    have hagg := aggEvalMF_sound s hs ps hag
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh
    have hcp : (0 : ℝ) ≤ cpi := by exact_mod_cast hcpi
    have hB : (lo : ℝ) ≤ ∑ m ∈ range n,
        ((coeffs (addL (cellPoly C cpi zc dd) [α, β]) m : ℚ) : ℝ) * s ^ m := by
      have hw2 : (0 : ℚ) < 2 * h := by linarith
      have hsR : |s| ≤ (h : ℝ) := hs
      have := bernLoOk_sound_real (a := coeffs (addL (cellPoly C cpi zc dd) [α, β])) (d := n - 1)
        (u := -h) (w := 2 * h) hw2 hbern
        (x := s) (by push_cast; linarith [(abs_le.1 hsR).1]) (by push_cast; linarith [(abs_le.1 hsR).2])
      have e : n - 1 + 1 = n := by omega
      unfold peval at this
      rw [e] at this
      exact this
    have hsplit : ∑ m ∈ range n, ((coeffs (addL (cellPoly C cpi zc dd) [α, β]) m : ℚ) : ℝ) * s ^ m
        = ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m + (cpi : ℝ) * ((zc.im : ℝ) + s * dd.im)
          + ((α : ℝ) + β * s) := by
      rw [sum_coeffs_addL, sum_coeffs_lin α β n hn2]
      unfold cellPoly
      rw [sum_coeffs_addL, sum_coeffs_lin (cpi * zc.im) (cpi * dd.im) n hn2]
      push_cast; ring
    have hz : ‖(zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ))‖ ≤ (W : ℝ) := by
      have : (zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) = -(δ : ℂ) := by ring
      rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hδ
    have hms := modAll_sum hWR ps hmod hz
    have him : (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im = (zc.im : ℝ) + s * (dd.im : ℝ) := by
      simp [CQ.toC]
    have hy : 0 ≤ (zc.im : ℝ) + s * dd.im := by
      have h1 : |s * (dd.im : ℝ)| ≤ h * |(dd.im : ℝ)| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      have h2 := (abs_le.1 h1).1
      have h0 : (0 : ℝ) ≤ (zc.im : ℝ) - h * |(dd.im : ℝ)| := by exact_mod_cast hy0
      linarith
    rw [him, abs_of_nonneg hy]
    have hfinR : (m' : ℝ) ≤ lo - Fs - modSum Rtwo W eW eP ps := by exact_mod_cast hfin
    have hFR : (F0 : ℝ) ≤ Fs := by exact_mod_cast hF
    rw [abs_le] at hagg hms
    rw [hsplit] at hB
    nlinarith [hagg.1, hagg.2, hms.1, hms.2, hFR]
  · cases hc

end CatalanCore.Uniform.Decay.FarField
