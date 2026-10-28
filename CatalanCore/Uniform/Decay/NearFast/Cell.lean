import CatalanCore.Uniform.Decay.NearFast.Agg
set_option Elab.async false

/-!
# Cell rules with the fast model (lane D, package D12)

`cellOkF` and `mixOkF` are `NearCells.cellOk'` and `NearCells.mixOk` with `aggEvalM` replaced by the
fast `aggEvalMF`.  The soundness statements are identical to `cellOk'_sound` and `mixOk_sound`, so
they are drop-in cell kinds: the proofs are those of the original rules with `aggEvalMF_sound` in
place of `aggEvalM_sound`.  The supplied aggregate `C` is the rounded model computed by `aggEvalMF`
(a rational with denominator dividing `12 * GG`-scale products; generate it by `#eval`).
-/

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells

/-- The cell rule.  The aggregate model `C` (exact, as a literal), an upper bound `Fs` of its error,
and `lo` (a lower bound of the Bernstein polynomial) are data; `aggEval` is run once to verify
`C` and `Fs`, and everything else is computed on the literals. -/
def cellOkF (n : ℕ) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi lo m' : ℚ) (C : List ℚ) (Fs : ℚ)
    (eW eP : ℕ) : Bool :=
  match aggEvalMF n zc dd h ps with
  | some (C0, F0) =>
    decide (0 < h) && decide (h ≤ 1) && decide (0 < W) && decide (0 ≤ cpi) && decide (2 ≤ n) &&
      decide (0 ≤ zc.im - h * |dd.im|) && decide (C0 = C) && decide (F0 ≤ Fs) &&
      bernLoOk2 (coeffs (cellPoly C cpi zc dd)) (n - 1) (-h) (2 * h) lo &&
      modAll Rtwo W eW eP ps &&
      decide (m' ≤ lo - Fs - modSum Rtwo W eW eP ps)
  | none => false

/-- **The cell rule.** -/
theorem cellOkF_sound {n : ℕ} {ps : List WP} {zc dd : CQ} {h W Rtwo cpi lo m' : ℚ} {C : List ℚ}
    {Fs : ℚ} {eW eP : ℕ}
    (hc : cellOkF n ps zc dd h W Rtwo cpi lo m' C Fs eW eP = true) (s δ : ℝ) (hs : |s| ≤ h)
    (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold cellOkF at hc
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

def mixOkF (n : ℕ) (far near : List WP) (zc dd : CQ) (h ρ W Rtwo cpi lo m' : ℚ) (C : List ℚ)
    (Fs : ℚ) (eW eP eW' eP' : ℕ) : Bool :=
  match aggEvalMF n zc dd h far, aggEvalMF n zc ⟨1, 0⟩ 0 near with
  | some (C0, F0), some (Cn, Fn) =>
    decide (0 < h) && decide (h ≤ 1) && decide (0 < W) && decide (0 ≤ cpi) && decide (2 ≤ n) &&
      decide (0 ≤ zc.im - h * |dd.im|) && decide (h * (|dd.re| + |dd.im|) + W ≤ ρ) &&
      decide (addL C0 [coeffs Cn 0] = C) && decide (F0 + Fn ≤ Fs) &&
      bernLoOk2 (coeffs (cellPoly C cpi zc dd)) (n - 1) (-h) (2 * h) lo &&
      modAll Rtwo W eW eP far && modAll Rtwo ρ eW' eP' near &&
      decide (m' ≤ lo - Fs - modSum Rtwo W eW eP far - modSum Rtwo ρ eW' eP' near)
  | _, _ => false

theorem mixOkF_sound {n : ℕ} {far near : List WP} {zc dd : CQ} {h ρ W Rtwo cpi lo m' : ℚ}
    {C : List ℚ} {Fs : ℚ} {eW eP eW' eP' : ℕ}
    (hc : mixOkF n far near zc dd h ρ W Rtwo cpi lo m' C Fs eW eP eW' eP' = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -((far ++ near).map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold mixOkF at hc
  split at hc
  · rename_i C0 F0 Cn Fn hag hagn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hh1⟩, hW⟩, hcpi⟩, hn2⟩, hy0⟩, hρ⟩, hcl⟩, hF⟩, hbern⟩, hmodF⟩,
      hmodN⟩, hfin⟩ := hc
    have hbern := bernLoOk2_imp hbern
    have hagg := aggEvalMF_sound s hs far hag
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh
    have hcp : (0 : ℝ) ≤ cpi := by exact_mod_cast hcpi
    have hsR : |s| ≤ (h : ℝ) := hs
    -- the near value at the centre
    have haggn := aggEvalMF_sound (n := n) (zc := zc) (dd := ⟨1, 0⟩) (h := 0) 0 (by simp) near hagn
    have hC0 : ∑ m ∈ range n, ((coeffs Cn m : ℚ) : ℝ) * (0 : ℝ) ^ m = ((coeffs Cn 0 : ℚ) : ℝ) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Finset.sum_range_succ']
      simp
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at haggn
    rw [hC0] at haggn
    -- Bernstein on the cell polynomial
    have hB : (lo : ℝ) ≤ ∑ m ∈ range n, ((coeffs (cellPoly C cpi zc dd) m : ℚ) : ℝ) * s ^ m := by
      have hw2 : (0 : ℚ) < 2 * h := by linarith
      have := bernLoOk_sound_real (a := coeffs (cellPoly C cpi zc dd)) (d := n - 1) (u := -h)
        (w := 2 * h) hw2 hbern
        (x := s) (by push_cast; linarith [(abs_le.1 hsR).1]) (by push_cast; linarith [(abs_le.1 hsR).2])
      have e : n - 1 + 1 = n := by omega
      unfold peval at this
      rw [e] at this
      exact this
    have hCsum : ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m
        = ∑ m ∈ range n, ((coeffs C0 m : ℚ) : ℝ) * s ^ m + ((coeffs Cn 0 : ℚ) : ℝ) := by
      rw [← hcl]
      have h1 : ∀ m ∈ range n, ((coeffs (addL C0 [coeffs Cn 0]) m : ℚ) : ℝ) * s ^ m
          = ((coeffs C0 m : ℚ) : ℝ) * s ^ m + ((coeffs [coeffs Cn 0] m : ℚ) : ℝ) * s ^ m := by
        intro m _
        rw [coeffs_addL]; push_cast; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Finset.sum_range_succ']
      have h3 : ∀ m ∈ range k, ((coeffs [coeffs Cn 0] (m + 1) : ℚ) : ℝ) * s ^ (m + 1) = 0 := by
        intro m _; simp [coeffs]
      rw [Finset.sum_eq_zero h3]
      simp [coeffs]
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
    -- far modulus (transverse, radius W)
    have hz : ‖(zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ))‖ ≤ (W : ℝ) := by
      have : (zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) = -(δ : ℂ) := by ring
      rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hδ
    have hmsF := modAll_sum hWR far hmodF hz
    -- near modulus (ball of radius ρ around the centre)
    have hρR : (0 : ℝ) < ρ := by
      have : (0 : ℚ) < ρ := by
        have h1 : 0 ≤ h * (|dd.re| + |dd.im|) := mul_nonneg hh.le (add_nonneg (abs_nonneg _) (abs_nonneg _))
        linarith
      exact_mod_cast this
    have hzn : ‖zc.toC - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ))‖ ≤ (ρ : ℝ) := by
      have e : zc.toC - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) = -((s : ℂ) * dd.toC + (δ : ℂ)) := by ring
      rw [e, norm_neg]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖dd.toC‖ ≤ |(dd.re : ℝ)| + |(dd.im : ℝ)| := Complex.norm_le_abs_re_add_abs_im _
      have h2 : |s| * ‖dd.toC‖ ≤ (h : ℝ) * (|(dd.re : ℝ)| + |(dd.im : ℝ)|) :=
        mul_le_mul hsR h1 (norm_nonneg _) hhR.le
      have h3 : (h : ℝ) * (|(dd.re : ℝ)| + |(dd.im : ℝ)|) + W ≤ ρ := by exact_mod_cast hρ
      linarith
    have hmsN := modAll_sum hρR near hmodN hzn
    -- imaginary part
    have him : (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im = (zc.im : ℝ) + s * (dd.im : ℝ) := by
      simp [CQ.toC]
    have hy : 0 ≤ (zc.im : ℝ) + s * dd.im := by
      have h1 : |s * (dd.im : ℝ)| ≤ h * |(dd.im : ℝ)| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      have h2 := (abs_le.1 h1).1
      have h0 : (0 : ℝ) ≤ (zc.im : ℝ) - h * |(dd.im : ℝ)| := by exact_mod_cast hy0
      linarith
    rw [him, abs_of_nonneg hy, List.map_append, List.sum_append]
    have hfinR : (m' : ℝ) ≤ lo - Fs - modSum Rtwo W eW eP far - modSum Rtwo ρ eW' eP' near := by
      exact_mod_cast hfin
    have hFR : (F0 : ℝ) + Fn ≤ Fs := by exact_mod_cast hF
    rw [abs_le] at hagg hmsF hmsN haggn
    rw [hsplit, hCsum] at hB
    nlinarith [hagg.1, hagg.2, hmsF.1, hmsF.2, hmsN.1, hmsN.2, haggn.1, haggn.2, hFR]
  · cases hc

/-- `mixOkF_sound` for the whole piece list `ps` given as a permutation of `far ++ near`
(e.g. through `splitSel`). -/
theorem mixOkF_sound_perm {n : ℕ} {ps far near : List WP} {zc dd : CQ} {h ρ W Rtwo cpi lo m' : ℚ}
    {C : List ℚ} {Fs : ℚ} {eW eP eW' eP' : ℕ} (hp : ps.Perm (far ++ near))
    (hc : mixOkF n far near zc dd h ρ W Rtwo cpi lo m' C Fs eW eP eW' eP' = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  rw [(hp.map _).sum_eq]
  exact mixOkF_sound hc s δ hs hδ

end CatalanCore.Uniform.Decay.NearFast
