module

public import CatalanCore.Uniform.Decay.NearCells.Piece

@[expose] public section

/-!
# `piece_model` (lane D, package D6b)
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset Complex CatalanCore.Uniform.Decay.Tools

/-- Real coefficient `c_m` of the model polynomial (depends on `L₀ = Log(-ζ₀)`, `L₁ = Log(1-ζ₀)`). -/
noncomputable def cmodel (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (L0 L1 : ℂ) (m : ℕ) : ℝ :=
  ((PAc a d z0 e m).toC * L1 + (PBc a d z0 e m).toC * L0 + (Rc a d z0 e m).toC
    + (jetc (PAc a d z0 e) (q1of z0 e) m).toC + (jetc (PBc a d z0 e) (q0of z0 e) m).toC).re

theorem norm_le_of_nsq {q : CQ} {h r : ℚ} (hh : 0 ≤ h) (hr : 0 ≤ r) (hq : q.nsq * h ^ 2 ≤ r ^ 2) :
    ‖q.toC‖ * (h : ℝ) ≤ (r : ℝ) := by
  have hq' : (q.nsq : ℝ) * (h : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by exact_mod_cast hq
  have hn : ‖q.toC‖ ^ 2 = (q.nsq : ℝ) := by
    rw [Complex.sq_norm, ← CQ.nsq_cast]
  have hh' : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  by_contra hc
  push_neg at hc
  have h0 : 0 ≤ ‖q.toC‖ * (h : ℝ) := mul_nonneg (norm_nonneg _) hh'
  have : (r : ℝ) ^ 2 < (‖q.toC‖ * (h : ℝ)) ^ 2 := by nlinarith
  have e2 : (‖q.toC‖ * (h : ℝ)) ^ 2 = (q.nsq : ℝ) * (h : ℝ) ^ 2 := by rw [mul_pow, hn]
  linarith

theorem re_one_sub_pos {q : ℂ} {s : ℝ} {h r : ℝ} (hs : |s| ≤ h) (hq : ‖q‖ * h ≤ r) (hr : r < 1) :
    0 < (1 - q * (s : ℂ)).re := by
  have h1 : ‖q * (s : ℂ)‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖q‖ * |s| ≤ ‖q‖ * h := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ ≤ r := hq
  have h2 := Complex.abs_re_le_norm (q * (s : ℂ))
  have h3 := (abs_le.1 (h2.trans h1)).2
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem log_mul_of_im_mul_pos {X b : ℂ} (hX : X ≠ 0) (hb : 0 < b.re)
    (h : 0 < X.im * (X * b).im ∨ (X.im = 0 ∧ (X * b).im = 0)) :
    Complex.log (X * b) = Complex.log X + Complex.log b := by
  rcases h with h | ⟨h1, h2⟩
  · rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact log_mul_of_im_nonneg hX hb h1.le h2.le
    · exact log_mul_of_im_neg hX hb h1 h2
  · exact log_mul_of_im_nonneg hX hb h1.ge h2.ge

/-- **The model of one segment's potential on a line cell.** -/
theorem piece_model (a : ℕ → ℚ) (d n : ℕ) (hn : d + 2 ≤ n) (A B zc dd : CQ) (h rq0 rq1 : ℚ)
    (hh : 0 ≤ h) (hv : (CQ.sub B A).nsq ≠ 0)
    (hz0nsq : (z0of A B zc).nsq ≠ 0) (h1z0nsq : (CQ.sub CQ.one (z0of A B zc)).nsq ≠ 0)
    (hside : sideOk (z0of A B zc) (eof A B dd) h = true)
    (hr0 : 0 ≤ rq0) (hr0' : rq0 < 1)
    (hq0 : (q0of (z0of A B zc) (eof A B dd)).nsq * h ^ 2 ≤ rq0 ^ 2)
    (hr1 : 0 ≤ rq1) (hr1' : rq1 < 1)
    (hq1 : (q1of (z0of A B zc) (eof A B dd)).nsq * h ^ 2 ≤ rq1 ^ 2)
    (s : ℝ) (hs : |s| ≤ h) :
    |(∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), (a k : ℝ) * t ^ k) *
        Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (A.toC + (t : ℂ) * (B.toC - A.toC))‖)
      - ((massQ a d : ℝ) * Real.log ‖B.toC - A.toC‖ +
        ∑ m ∈ range n, cmodel a d (z0of A B zc) (eof A B dd)
          (Complex.log (-(z0of A B zc).toC)) (Complex.log (1 - (z0of A B zc).toC)) m * s ^ m)|
    ≤ (jbQ (PAc a d (z0of A B zc) (eof A B dd)) n rq1 h : ℝ)
      + (jbQ (PBc a d (z0of A B zc) (eof A B dd)) n rq0 h : ℝ) := by
  set z0 := z0of A B zc with hz0def
  set e := eof A B dd with hedef
  have hBA : B.toC - A.toC ≠ 0 := by rw [← CQ.toC_sub]; exact CQ.toC_ne_zero hv
  have hz0 : z0.toC = (zc.toC - A.toC) / (B.toC - A.toC) := by
    rw [hz0def]; unfold z0of; rw [CQ.toC_div _ _ hv, CQ.toC_sub, CQ.toC_sub]
  have he : e.toC = dd.toC / (B.toC - A.toC) := by
    rw [hedef]; unfold eof; rw [CQ.toC_div _ _ hv, CQ.toC_sub]
  have hζ : ((zc.toC + (s : ℂ) * dd.toC) - A.toC) / (B.toC - A.toC) = z0.toC + e.toC * (s : ℂ) := by
    rw [hz0, he]; field_simp; ring
  have hsd := sideOk_sound hside s hs
  have hq0C : (q0of z0 e).toC = -(e.toC / z0.toC) := by
    unfold q0of; rw [CQ.toC_neg, CQ.toC_div _ _ hz0nsq]
  have hq1C : (q1of z0 e).toC = e.toC / (1 - z0.toC) := by
    unfold q1of; rw [CQ.toC_div _ _ h1z0nsq, CQ.toC_sub, CQ.toC_one]
  have hz0ne : z0.toC ≠ 0 := CQ.toC_ne_zero hz0nsq
  have h1z0ne : 1 - z0.toC ≠ 0 := by
    have := CQ.toC_ne_zero h1z0nsq
    rwa [CQ.toC_sub, CQ.toC_one] at this
  have hn0 := norm_le_of_nsq hh hr0 hq0
  have hn1 := norm_le_of_nsq hh hr1 hq1
  have hr0R : (rq0 : ℝ) < 1 := by exact_mod_cast hr0'
  have hr1R : (rq1 : ℝ) < 1 := by exact_mod_cast hr1'
  have hsR : |s| ≤ (h : ℝ) := hs
  have hre0 := re_one_sub_pos (q := (q0of z0 e).toC) hsR hn0 hr0R
  have hre1 := re_one_sub_pos (q := (q1of z0 e).toC) hsR hn1 hr1R
  -- branch splitting
  have hfac1 : 1 - (z0.toC + e.toC * (s : ℂ)) = (1 - z0.toC) * (1 - (q1of z0 e).toC * (s : ℂ)) := by
    rw [hq1C]; field_simp; ring
  have hfac0 : -(z0.toC + e.toC * (s : ℂ)) = (-z0.toC) * (1 - (q0of z0 e).toC * (s : ℂ)) := by
    rw [hq0C]; field_simp; ring
  have hlog1 : Complex.log (1 - (z0.toC + e.toC * (s : ℂ))) =
      Complex.log (1 - z0.toC) + Complex.log (1 - (q1of z0 e).toC * (s : ℂ)) := by
    rw [hfac1]
    apply log_mul_of_im_mul_pos h1z0ne hre1
    rw [← hfac1]
    have e1 : (1 - z0.toC).im = -(z0.im : ℝ) := by simp [CQ.toC]
    have e2 : (1 - (z0.toC + e.toC * (s : ℂ))).im = -(z0.toC + e.toC * (s : ℂ)).im := by simp
    rw [e1, e2]
    rcases hsd with h | ⟨h0, h1⟩
    · left; nlinarith [h]
    · right; rw [h0, h1]; simp
  have hlog0 : Complex.log (-(z0.toC + e.toC * (s : ℂ))) =
      Complex.log (-z0.toC) + Complex.log (1 - (q0of z0 e).toC * (s : ℂ)) := by
    rw [hfac0]
    apply log_mul_of_im_mul_pos (neg_ne_zero.2 hz0ne) hre0
    rw [← hfac0]
    have e1 : (-z0.toC).im = -(z0.im : ℝ) := by simp [CQ.toC]
    have e2 : (-(z0.toC + e.toC * (s : ℂ))).im = -(z0.toC + e.toC * (s : ℂ)).im := by simp
    rw [e1, e2]
    rcases hsd with h | ⟨h0, h1⟩
    · left; nlinarith [h]
    · right; rw [h0, h1]; simp
  have hI := potential_closed a d A.toC B.toC (zc.toC + (s : ℂ) * dd.toC) hBA
  rw [hI, hζ, hlog1, hlog0, ← PA_expand a d z0 e (s : ℂ) n hn, ← PB_expand a d z0 e (s : ℂ) n hn,
    ← R_expand a d z0 e (s : ℂ) n (by omega)]
  set PAf : ℕ → ℂ := fun j => (PAc a d z0 e j).toC with hPAf
  set PBf' : ℕ → ℂ := fun j => (PBc a d z0 e j).toC with hPBf
  set L1 := Complex.log (1 - z0.toC) with hL1
  set L0 := Complex.log (-z0.toC) with hL0
  set LA := Complex.log (1 - (q1of z0 e).toC * (s : ℂ)) with hLA
  set LB := Complex.log (1 - (q0of z0 e).toC * (s : ℂ)) with hLB
  have hJA : jet n PAf (q1of z0 e).toC (s : ℂ) = ∑ m ∈ range n, (jetc (PAc a d z0 e) (q1of z0 e) m).toC * (s : ℂ) ^ m :=
    jet_expand (PAc a d z0 e) (q1of z0 e) (s : ℂ) n
  have hJB : jet n PBf' (q0of z0 e).toC (s : ℂ) = ∑ m ∈ range n, (jetc (PBc a d z0 e) (q0of z0 e) m).toC * (s : ℂ) ^ m :=
    jet_expand (PBc a d z0 e) (q0of z0 e) (s : ℂ) n
  have hcm : ∑ m ∈ range n, cmodel a d z0 e L0 L1 m * s ^ m
      = ((∑ m ∈ range n, PAf m * (s : ℂ) ^ m) * L1 + (∑ m ∈ range n, PBf' m * (s : ℂ) ^ m) * L0
        + (∑ m ∈ range n, (Rc a d z0 e m).toC * (s : ℂ) ^ m)
        + jet n PAf (q1of z0 e).toC (s : ℂ) + jet n PBf' (q0of z0 e).toC (s : ℂ)).re := by
    rw [hJA, hJB]
    have h1 : ∀ m ∈ range n, cmodel a d z0 e L0 L1 m * s ^ m
        = (((PAc a d z0 e m).toC * L1 + (PBc a d z0 e m).toC * L0 + (Rc a d z0 e m).toC
          + (jetc (PAc a d z0 e) (q1of z0 e) m).toC + (jetc (PBc a d z0 e) (q0of z0 e) m).toC)
          * (s : ℂ) ^ m).re := by
      intro m _
      unfold cmodel
      rw [show (s : ℂ) ^ m = ((s ^ m : ℝ) : ℂ) by push_cast; rfl, Complex.re_mul_ofReal]
    rw [Finset.sum_congr rfl h1, ← Complex.re_sum]
    congr 1
    have h2 : ∀ m ∈ range n, ((PAc a d z0 e m).toC * L1 + (PBc a d z0 e m).toC * L0
        + (Rc a d z0 e m).toC + (jetc (PAc a d z0 e) (q1of z0 e) m).toC
        + (jetc (PBc a d z0 e) (q0of z0 e) m).toC) * (s : ℂ) ^ m
        = (PAc a d z0 e m).toC * (s : ℂ) ^ m * L1 + (PBc a d z0 e m).toC * (s : ℂ) ^ m * L0
          + (Rc a d z0 e m).toC * (s : ℂ) ^ m
          + (jetc (PAc a d z0 e) (q1of z0 e) m).toC * (s : ℂ) ^ m
          + (jetc (PBc a d z0 e) (q0of z0 e) m).toC * (s : ℂ) ^ m := by
      intro m _; ring
    rw [Finset.sum_congr rfl h2]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  rw [hcm]
  have hsC : ‖(s : ℂ)‖ ≤ (h : ℝ) := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hs
  have rA := norm_jet_remainder_le n PAf hsC (q := (q1of z0 e).toC) (by
    have := hn1; linarith)
  have rB := norm_jet_remainder_le n PBf' hsC (q := (q0of z0 e).toC) (by
    have := hn0; linarith)
  have bA := jetBound_le_jbQ (q := (q1of z0 e).toC) (PAc a d z0 e) n hh hn1 hr1'
  have bB := jetBound_le_jbQ (q := (q0of z0 e).toC) (PBc a d z0 e) n hh hn0 hr0'
  set PAs := ∑ m ∈ range n, PAf m * (s : ℂ) ^ m
  set PBs := ∑ m ∈ range n, PBf' m * (s : ℂ) ^ m
  set Rs := ∑ m ∈ range n, (Rc a d z0 e m).toC * (s : ℂ) ^ m
  have hdiff : (↑(massQ a d : ℝ) * Real.log ‖B.toC - A.toC‖
        + (PAs * (L1 + LA) + PBs * (L0 + LB) + Rs).re) -
      (↑(massQ a d : ℝ) * Real.log ‖B.toC - A.toC‖ +
        (PAs * L1 + PBs * L0 + Rs + jet n PAf (q1of z0 e).toC (s : ℂ)
          + jet n PBf' (q0of z0 e).toC (s : ℂ)).re)
      = ((PAs * LA - jet n PAf (q1of z0 e).toC (s : ℂ))
          + (PBs * LB - jet n PBf' (q0of z0 e).toC (s : ℂ))).re := by
    rw [add_sub_add_left_eq_sub, ← Complex.sub_re]
    congr 1
    ring
  rw [hdiff]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have := add_le_add (rA.trans bA) (rB.trans bB)
  linarith

end CatalanCore.Uniform.Decay.NearCells
