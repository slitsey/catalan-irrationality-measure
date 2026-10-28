import CatalanCore.Uniform.Decay.Breakpoint.IncEval
import CatalanCore.Uniform.Decay.Breakpoint.Rev
import CatalanCore.Uniform.Decay.Breakpoint.LogB
import CatalanCore.Uniform.Decay.NearFast.Cell
set_option Elab.async false

/-!
# The breakpoint cell rule (lane D, package D14)

A *breakpoint cell* is a cell `[ulo, uhi]` of a polygon edge (or a line/cap cell) one of whose ends is
a breakpoint `p` of the piecewise polynomial density (an endpoint of pieces, a corner or the end of
the contour).  Along the contour parameter `s ≥ 0` measured from `p` the potential is

`-∑ w_P Φ_P(p + s d) = (poly in s) + ln s · (poly in s) + remainder`,

with an explicit remainder bound valid on the whole interval `[0, S]` (`bpLine`).  The pieces that
neither start nor end at `p` are handled by the accepted fast jet `aggEvalMF` about `p` (radius `S`);
the pieces that start at `p` by `incAgg`; the pieces that end at `p` are reversed (`revWP`) first.

`bpOk` is the cell Boolean (`side = false`: `p` is the left end `zc - h dd`, `side = true`: the right
end `zc + h dd`); `bpOk_sound` has the statement of `cellOkF_sound`, so it is a new cell kind.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells
  CatalanCore.Uniform.Decay.NearFast

/-- `p` lies on the line of `P` beyond its end `B` (`ζ₀ = (p - A)/(B - A)` real and `> 1`).  Such a piece is
reversed: then `ζ₀' = 1 - ζ₀ < 0`, the case the fast jet handles on both sides of `p`, whatever the direction. -/
def needRev (p : CQ) (P : WP) : Bool :=
  decide ((z0of P.A P.B p).im = 0) && decide (1 < (z0of P.A P.B p).re)

/-- The pieces that neither start nor end at `p` (those with `p` on their line beyond `B` reversed). -/
def bpFar (p : CQ) (ps : List WP) : List WP :=
  ((ps.filter (fun P => !cqEq P.A p)).filter (fun P => !cqEq P.B p)).map
    (fun P => if needRev p P then revWP P else P)

/-- The pieces that start at `p`, then the (reversed) pieces that end at `p`. -/
def bpInc (p : CQ) (ps : List WP) : List WP :=
  ps.filter (fun P => cqEq P.A p) ++
    ((ps.filter (fun P => !cqEq P.A p)).filter (fun P => cqEq P.B p)).map revWP

theorem sum_split (q : WP → Bool) (l : List WP) (F : WP → ℝ) :
    (l.map F).sum = ((l.filter q).map F).sum + ((l.filter (fun x => !q x)).map F).sum := by
  rw [← ((List.filter_append_perm q l).map F).sum_eq]
  simp [List.map_append, List.sum_append]

theorem bp_sum (p : CQ) (ps : List WP) (z : ℂ) :
    (ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum
      = ((bpFar p ps).map (fun P => (P.w : ℝ) * PhiW P z)).sum
        + ((bpInc p ps).map (fun P => (P.w : ℝ) * PhiW P z)).sum := by
  set F : WP → ℝ := fun P => (P.w : ℝ) * PhiW P z with hF
  have h1 := sum_split (fun P => cqEq P.A p) ps F
  have h2 := sum_split (fun P => cqEq P.B p) (ps.filter (fun P => !cqEq P.A p)) F
  have h3 : (((ps.filter (fun P => !cqEq P.A p)).filter (fun P => cqEq P.B p)).map revWP).map F
      = ((ps.filter (fun P => !cqEq P.A p)).filter (fun P => cqEq P.B p)).map F := by
    rw [List.map_map]
    refine List.map_congr_left fun P _ => ?_
    simp only [Function.comp, hF]
    rw [PhiW_revWP]
    rfl
  have h4 : (((ps.filter (fun P => !cqEq P.A p)).filter (fun P => !cqEq P.B p)).map
        (fun P => if needRev p P then revWP P else P)).map F
      = ((ps.filter (fun P => !cqEq P.A p)).filter (fun P => !cqEq P.B p)).map F := by
    rw [List.map_map]
    refine List.map_congr_left fun P _ => ?_
    by_cases hr : needRev p P = true
    · have hq : (if needRev p P then revWP P else P) = revWP P := by simp [hr]
      simp only [Function.comp, hq, hF]
      rw [PhiW_revWP]
      rfl
    · have hq : (if needRev p P then revWP P else P) = P := by simp [hr]
      simp only [Function.comp, hq]
  unfold bpFar bpInc
  rw [List.map_append, List.sum_append, h3, h4, h1, h2]
  ring

theorem bpInc_A (p : CQ) (ps : List WP) : ∀ P ∈ bpInc p ps, P.A.toC = p.toC := by
  intro P hP
  unfold bpInc at hP
  rcases List.mem_append.1 hP with h | h
  · exact cqEq_toC (List.mem_filter.1 h).2
  · obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 h
    exact cqEq_toC (List.mem_filter.1 hQ).2

/-- Expansion part of the breakpoint rule: the model about `p` along `d'` on `[0, S]`. -/
def bpLine (n : ℕ) (ps : List WP) (p d' : CQ) (S cpi lo : ℚ) (C : List ℚ) (Fs : ℚ) (eS : ℕ) : Bool :=
  match aggEvalMF n p d' S (bpFar p ps), incAgg n d' S (bpInc p ps) with
  | some (Cf, Ff), some (Ci, Bi, Fi) =>
    decide (0 < S) && decide (S ≤ 1 / 3) && decide (2 ≤ n) && decide (addL Cf Ci = C) &&
      decide (coeffs Bi 0 = 0) && decide (1 ≤ S * 2 ^ eS) &&
      decide (Ff + Fi + lsum (fun m => |coeffs Bi m| * S ^ m) n * (eS * (7 / 10)) ≤ Fs) &&
      bernLoOk2 (coeffs (cellPoly C cpi p d')) (n - 1) 0 S lo
  | _, _ => false

theorem bpLine_sound {n : ℕ} {ps : List WP} {p d' : CQ} {S cpi lo : ℚ} {C : List ℚ} {Fs : ℚ}
    {eS : ℕ} (hc : bpLine n ps p d' S cpi lo C Fs eS = true) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s ≤ (S : ℝ)) :
    (lo : ℝ) - Fs ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (p.toC + (s : ℂ) * d'.toC))).sum
      + (cpi : ℝ) * ((p.im : ℝ) + s * (d'.im : ℝ)) := by
  unfold bpLine at hc
  split at hc
  · rename_i Cf Ff Ci Bi Fi hag hinc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hS0, hS3⟩, hn2⟩, hCeq⟩, hB0⟩, hexp⟩, hFs⟩, hbern⟩ := hc
    have hbern := bernLoOk2_imp hbern
    have hSR : (0 : ℝ) < S := by exact_mod_cast hS0
    have hS3R : (S : ℝ) ≤ 1 / 3 := by
      have := (Rat.cast_le (K := ℝ)).2 hS3
      push_cast at this
      exact this
    have habs : |s| ≤ (S : ℝ) := by rw [abs_of_nonneg hs0]; exact hs
    have hagg := aggEvalMF_sound (zc := p) (dd := d') (h := S) s habs (bpFar p ps) hag
    have hincs := incAgg_sound (n := n) (dd := d') (h := S) (pc := p.toC) s hs0 hs (bpInc p ps)
      (bpInc_A p ps) hinc
    rw [bp_sum p ps]
    -- Bernstein on the cell polynomial
    have hB : (lo : ℝ) ≤ ∑ m ∈ range n, ((coeffs (cellPoly C cpi p d') m : ℚ) : ℝ) * s ^ m := by
      have := bernLoOk_sound_real (a := coeffs (cellPoly C cpi p d')) (d := n - 1) (u := 0)
        (w := S) hS0 hbern (x := s) (by push_cast; exact hs0) (by push_cast; linarith)
      have e : n - 1 + 1 = n := by omega
      unfold peval at this
      rw [e] at this
      exact this
    have hsplit : ∑ m ∈ range n, ((coeffs (cellPoly C cpi p d') m : ℚ) : ℝ) * s ^ m
        = ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m
          + (cpi : ℝ) * ((p.im : ℝ) + s * d'.im) := by
      have h1 : ∀ m ∈ range n, ((coeffs (cellPoly C cpi p d') m : ℚ) : ℝ) * s ^ m
          = ((coeffs C m : ℚ) : ℝ) * s ^ m
            + ((coeffs [cpi * p.im, cpi * d'.im] m : ℚ) : ℝ) * s ^ m := by
        intro m _
        unfold cellPoly
        rw [coeffs_addL]; push_cast; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have h3 : ∀ m ∈ range k,
          ((coeffs [cpi * p.im, cpi * d'.im] (m + 1 + 1) : ℚ) : ℝ) * s ^ (m + 1 + 1) = 0 := by
        intro m _; simp [coeffs]
      rw [Finset.sum_eq_zero h3]
      simp [coeffs]; ring
    have hCsum : ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m
        = ∑ m ∈ range n, ((coeffs Cf m : ℚ) : ℝ) * s ^ m
          + ∑ m ∈ range n, ((coeffs Ci m : ℚ) : ℝ) * s ^ m := by
      rw [← hCeq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeffs_addL]; push_cast; ring
    -- the logarithmic terms
    have hlogb : |Real.log s * ∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m|
        ≤ ((lsum (fun m => |coeffs Bi m| * S ^ m) n * (eS * (7 / 10)) : ℚ) : ℝ) := by
      have hlogS : |Real.log (S : ℝ)| ≤ (eS : ℝ) * (7 / 10) :=
        abs_log_le_of_pow hSR (by linarith) (by exact_mod_cast hexp)
      have hR : ((lsum (fun m => |coeffs Bi m| * S ^ m) n * (eS * (7 / 10)) : ℚ) : ℝ)
          = (∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m) * ((eS : ℝ) * (7 / 10)) := by
        rw [Rat.cast_mul, lsum_eq]
        push_cast
        rfl
      rw [hR]
      have hnn : 0 ≤ (∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m) :=
        Finset.sum_nonneg fun m _ => mul_nonneg (abs_nonneg _) (by positivity)
      rcases hs0.eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
        exact mul_nonneg hnn (by positivity)
      · have hterm : ∀ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ) * s ^ m * Real.log s|
            ≤ |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * |Real.log (S : ℝ)| := by
          intro m _
          by_cases hm : m = 0
          · subst hm
            have : ((coeffs Bi 0 : ℚ) : ℝ) = 0 := by rw [hB0]; simp
            rw [this]; simp
          · rw [abs_mul, abs_mul, abs_pow, abs_of_pos hpos, mul_assoc]
            have := pow_mul_abs_log_le (Nat.one_le_iff_ne_zero.2 hm) hpos hs (hS3R)
            calc |((coeffs Bi m : ℚ) : ℝ)| * (s ^ m * |Real.log s|)
                ≤ |((coeffs Bi m : ℚ) : ℝ)| * ((S : ℝ) ^ m * |Real.log (S : ℝ)|) :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = _ := by ring
        calc |Real.log s * ∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m|
            = |∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m * Real.log s| := by
              rw [mul_comm, Finset.sum_mul]
          _ ≤ ∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ) * s ^ m * Real.log s| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * |Real.log (S : ℝ)| :=
              Finset.sum_le_sum hterm
          _ = (∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m) * |Real.log (S : ℝ)| := by
              rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hlogS hnn
    have hFsR : (Ff : ℝ) + Fi + ((lsum (fun m => |coeffs Bi m| * S ^ m) n * (eS * (7 / 10)) : ℚ) : ℝ)
        ≤ Fs := by exact_mod_cast hFs
    rw [abs_le] at hagg hincs hlogb
    rw [hsplit, hCsum] at hB
    nlinarith [hagg.1, hagg.2, hincs.1, hincs.2, hlogb.1, hlogb.2, hFsR]
  · cases hc

/-! ### The cell rule -/

/-- The breakpoint `p` of a cell: its left end (`side = false`) or right end (`side = true`). -/
def bpPoint (side : Bool) (zc dd : CQ) (h : ℚ) : CQ :=
  if side then CQ.add zc (CQ.smul h dd) else CQ.sub zc (CQ.smul h dd)

/-- The direction leaving the breakpoint into the cell. -/
def bpDir (side : Bool) (dd : CQ) : CQ := if side then CQ.neg dd else dd

/-- **The breakpoint cell rule.**  Same data as `cellOkF` plus the side of the breakpoint and the
checked exponent `eS` (`1 ≤ 2h · 2^eS`).  `C` is the model about `p` in the distance `s` to `p`. -/
def bpOk (n : ℕ) (side : Bool) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi lo m' : ℚ) (C : List ℚ)
    (Fs : ℚ) (eW eP eS : ℕ) : Bool :=
  bpLine n ps (bpPoint side zc dd h) (bpDir side dd) (2 * h) cpi lo C Fs eS &&
    decide (0 < h) && decide (0 < W) && decide (0 ≤ cpi) && decide (0 ≤ zc.im - h * |dd.im|) &&
    modAll Rtwo W eW eP ps && decide (m' ≤ lo - Fs - modSum Rtwo W eW eP ps)

theorem bpLine_cell {n : ℕ} {side : Bool} {ps : List WP} {zc dd : CQ} {h cpi lo : ℚ} {C : List ℚ}
    {Fs : ℚ} {eS : ℕ}
    (hc : bpLine n ps (bpPoint side zc dd h) (bpDir side dd) (2 * h) cpi lo C Fs eS = true)
    (s : ℝ) (hs : |s| ≤ h) :
    (lo : ℝ) - Fs ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum
      + (cpi : ℝ) * ((zc.im : ℝ) + s * (dd.im : ℝ)) := by
  have hs' := abs_le.1 hs
  cases side
  · have := bpLine_sound hc (s + h) (by linarith [hs'.1]) (by push_cast; linarith [hs'.2])
    have hz : (bpPoint false zc dd h).toC + ((s + h : ℝ) : ℂ) * (bpDir false dd).toC
        = zc.toC + (s : ℂ) * dd.toC := by
      simp only [bpPoint, bpDir, Bool.false_eq_true, ↓reduceIte, CQ.toC_sub, CQ.toC_smul]
      push_cast; ring
    have hi : ((bpPoint false zc dd h).im : ℝ) + (s + h) * ((bpDir false dd).im : ℝ)
        = (zc.im : ℝ) + s * (dd.im : ℝ) := by
      simp only [bpPoint, bpDir, Bool.false_eq_true, ↓reduceIte, CQ.sub, CQ.smul]
      push_cast; ring
    rw [hz, hi] at this
    exact this
  · have := bpLine_sound hc (h - s) (by linarith [hs'.2]) (by push_cast; linarith [hs'.1])
    have hz : (bpPoint true zc dd h).toC + ((h - s : ℝ) : ℂ) * (bpDir true dd).toC
        = zc.toC + (s : ℂ) * dd.toC := by
      simp only [bpPoint, bpDir, ↓reduceIte, CQ.toC_add, CQ.toC_neg, CQ.toC_smul]
      push_cast; ring
    have hi : ((bpPoint true zc dd h).im : ℝ) + (h - s) * ((bpDir true dd).im : ℝ)
        = (zc.im : ℝ) + s * (dd.im : ℝ) := by
      simp only [bpPoint, bpDir, ↓reduceIte, CQ.add, CQ.smul, CQ.neg]
      push_cast; ring
    rw [hz, hi] at this
    exact this

/-- **The breakpoint cell rule** (statement of `cellOkF_sound`). -/
theorem bpOk_sound {n : ℕ} {side : Bool} {ps : List WP} {zc dd : CQ}
    {h W Rtwo cpi lo m' : ℚ} {C : List ℚ} {Fs : ℚ} {eW eP eS : ℕ}
    (hc : bpOk n side ps zc dd h W Rtwo cpi lo m' C Fs eW eP eS = true) (s δ : ℝ) (hs : |s| ≤ h)
    (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold bpOk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hline, hh⟩, hW⟩, hcpi⟩, hy0⟩, hmod⟩, hfin⟩ := hc
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hl := bpLine_cell hline s hs
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
  rw [abs_le] at hms
  nlinarith [hms.1, hms.2, hl, hfinR]

end CatalanCore.Uniform.Decay.Breakpoint
