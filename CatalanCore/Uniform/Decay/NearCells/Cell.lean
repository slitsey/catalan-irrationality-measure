import CatalanCore.Uniform.Decay.NearCells.Tube
set_option Elab.async false

/-!
# The generic cell rule along a segment (lane D, package D6b)

`cellOk`: all points `z = zc + s dd + δ` (`|s| ≤ h`, `|δ| ≤ W`) satisfy
`m' ≤ -∑ w_P Φ_P(z) + cπ |Im z|` -- the edge-parameter rule, generic over the segment
`s ↦ zc + s dd` (straight ray cells and polygon-edge tube cells alike).
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells

theorem affCoeffs_cast (a : ℕ → ℚ) (d : ℕ) (u w : ℚ) (j : ℕ) :
    ((affCoeffs a d u w j : ℚ) : ℝ) = affCoeffs (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ) j := by
  unfold affCoeffs
  push_cast
  rfl

theorem bernLoOk_sound_real {a : ℕ → ℚ} {d : ℕ} {u w lo : ℚ} (hw : 0 < w)
    (h : bernLoOk a d u w lo = true) {x : ℝ} (hx0 : (u : ℝ) ≤ x) (hx1 : x ≤ (u : ℝ) + w) :
    (lo : ℝ) ≤ peval (fun i => (a i : ℝ)) d x := by
  unfold bernLoOk at h
  rw [List.all_eq_true] at h
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hlo : ∀ k ≤ d, (lo : ℝ) ≤ bern (affCoeffs (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ)) d k := by
    intro k hk
    have := h k (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq, bernK_eq, affK_eq] at this
    have h2 : (lo : ℝ) ≤ ((bern (affCoeffs a d u w) d k : ℚ) : ℝ) := by exact_mod_cast this
    have e : ((bern (affCoeffs a d u w) d k : ℚ) : ℝ)
        = bern (affCoeffs (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ)) d k := by
      rw [← bern_cast]
      congr 1
      funext j
      exact affCoeffs_cast a d u w j
    rw [← e]; exact h2
  have hhi : ∀ k ≤ d, bern (affCoeffs (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ)) d k ≤
      ∑ j ∈ range (d + 1), |bern (affCoeffs (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ)) d j| := by
    intro k hk
    exact (le_abs_self _).trans (Finset.single_le_sum
      (f := fun j => |bern (affCoeffs (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ)) d j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  exact (bernstein_range_Icc (fun i => (a i : ℝ)) d (u : ℝ) (w : ℝ) hw' hlo hhi hx0 hx1).1

/-- Polynomial of the cell: aggregate model plus the linear term `cπ (Im zc + s Im dd)`. -/
def cellPoly (C : List ℚ) (cpi : ℚ) (zc dd : CQ) : List ℚ := addL C [cpi * zc.im, cpi * dd.im]

/-- The cell rule.  The aggregate model `C` (exact, as a literal), an upper bound `Fs` of its error,
and `lo` (a lower bound of the Bernstein polynomial) are data; `aggEval` is run once to verify
`C` and `Fs`, and everything else is computed on the literals. -/
def cellOk (n : ℕ) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi lo m' : ℚ) (C : List ℚ) (Fs : ℚ)
    (eW eP : ℕ) : Bool :=
  match aggEval n zc dd h ps with
  | some (C0, F0) =>
    decide (0 < h) && decide (h ≤ 1) && decide (0 < W) && decide (0 ≤ cpi) && decide (2 ≤ n) &&
      decide (0 ≤ zc.im - h * |dd.im|) && decide (C0 = C) && decide (F0 ≤ Fs) &&
      bernLoOk2 (coeffs (cellPoly C cpi zc dd)) (n - 1) (-h) (2 * h) lo &&
      modAll Rtwo W eW eP ps &&
      decide (m' ≤ lo - Fs - modSum Rtwo W eW eP ps)
  | none => false

theorem modAll_sum {Rtwo W : ℚ} {eW eP : ℕ} (hW : (0 : ℝ) < W) :
    ∀ (ps : List WP), modAll Rtwo W eW eP ps = true →
    ∀ {z z' : ℂ}, ‖z - z'‖ ≤ (W : ℝ) →
    |(ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum - (ps.map (fun P => (P.w : ℝ) * PhiW P z')).sum|
      ≤ (modSum Rtwo W eW eP ps : ℝ) := by
  intro ps
  induction ps with
  | nil => intro _ z z' _; simp [modSum]
  | cons P ps ih =>
    intro h z z' hzz
    simp only [modAll, List.all_cons, Bool.and_eq_true] at h
    have h1 := PhiW_modulus h.1 hzz
    have h2 := ih (by simpa [modAll] using h.2) hzz
    simp only [List.map_cons, List.sum_cons, modSum]
    push_cast
    have : (P.w : ℝ) * PhiW P z + (ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum
        - ((P.w : ℝ) * PhiW P z' + (ps.map (fun P => (P.w : ℝ) * PhiW P z')).sum)
        = (P.w : ℝ) * (PhiW P z - PhiW P z')
          + ((ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum
            - (ps.map (fun P => (P.w : ℝ) * PhiW P z')).sum) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ h2)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- **The cell rule.** -/
theorem cellOk_sound {n : ℕ} {ps : List WP} {zc dd : CQ} {h W Rtwo cpi lo m' : ℚ} {C : List ℚ}
    {Fs : ℚ} {eW eP : ℕ}
    (hc : cellOk n ps zc dd h W Rtwo cpi lo m' C Fs eW eP = true) (s δ : ℝ) (hs : |s| ≤ h)
    (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold cellOk at hc
  split at hc
  · rename_i C0 F0 hag
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hh1⟩, hW⟩, hcpi⟩, hn2⟩, hy0⟩, hcl⟩, hF⟩, hbern⟩, hmod⟩, hfin⟩ := hc
    have hcl' := hcl.symm
    subst hcl'
    have hbern := bernLoOk2_imp hbern
    have hagg := aggEval_sound s hs ps hag
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh
    have hcp : (0 : ℝ) ≤ cpi := by exact_mod_cast hcpi
    -- Bernstein on the cell polynomial
    have hB : (lo : ℝ) ≤ ∑ m ∈ range n, ((coeffs (cellPoly C cpi zc dd) m : ℚ) : ℝ) * s ^ m := by
      have hw2 : (0 : ℚ) < 2 * h := by linarith
      have hsR : |s| ≤ (h : ℝ) := hs
      have := bernLoOk_sound_real (a := coeffs (cellPoly C cpi zc dd)) (d := n - 1) (u := -h)
        (w := 2 * h) hw2 hbern
        (x := s) (by push_cast; linarith [(abs_le.1 hsR).1]) (by push_cast; linarith [(abs_le.1 hsR).2])
      have e : n - 1 + 1 = n := by omega
      unfold peval at this
      rw [e] at this
      exact this
    -- split the cell polynomial
    have hsplit : ∑ m ∈ range n, ((coeffs (cellPoly C cpi zc dd) m : ℚ) : ℝ) * s ^ m
        = ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m + (cpi : ℝ) * ((zc.im : ℝ) + s * dd.im) := by
      have h1 : ∀ m ∈ range n, ((coeffs (cellPoly C cpi zc dd) m : ℚ) : ℝ) * s ^ m
          = ((coeffs C m : ℚ) : ℝ) * s ^ m + ((coeffs [cpi * zc.im, cpi * dd.im] m : ℚ) : ℝ) * s ^ m := by
        intro m _
        unfold cellPoly
        rw [coeffs_addL]; push_cast; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have h3 : ∀ m ∈ range k, ((coeffs [cpi * zc.im, cpi * dd.im] (m + 1 + 1) : ℚ) : ℝ) * s ^ (m + 1 + 1) = 0 := by
        intro m _; simp [coeffs]
      rw [Finset.sum_eq_zero h3]
      simp [coeffs]; ring
    -- tube perturbation
    have hz : ‖(zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ))‖ ≤ (W : ℝ) := by
      have : (zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) = -(δ : ℂ) := by ring
      rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hδ
    have hms := modAll_sum hWR ps hmod hz
    -- imaginary part
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

end CatalanCore.Uniform.Decay.NearCells
