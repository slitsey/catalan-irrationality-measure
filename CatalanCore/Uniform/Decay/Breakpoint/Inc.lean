module

public import CatalanCore.Uniform.Decay.NearCells.PieceEval

@[expose] public section
set_option Elab.async false

/-!
# The potential of a segment that starts at the breakpoint (lane D, package D14)

Let `P` be the segment `A + t (B - A)` with polynomial density, and `z(s) = A + s dd`, `s ≥ 0`
(the field point leaves the *start* `A` of the segment along the direction `dd`).  Then
`ζ = e s`, `e = dd/(B - A)`, and the closed form of D1/D6b gives, exactly,

`Φ_P(z(s)) = mass log‖B - A‖ + Re( PA(es) Log(1 - es) + PB(es) Log(-es) + R(es) )`

with `Log(-es) = ln s + Log(-e)` for `s > 0`, and `PB(es) = O(s)`.  Expanding `PA(es) Log(1 - es)` as in
`piece_model` (D1's jet, ratio `‖e‖ s`) leaves a remainder `≤ jbQ (PA) n r h` on all of `[0, h]`:

`Φ_P(z(s)) = mass log‖B - A‖ + ∑_{m<n} c_m s^m + ln s ∑_{m<n} b_m s^m + rem`,
`b_m = Re PB_m`, `c_m = Re (PB_m Log(-e) + R_m + jet_m)`.

`incEval` computes rational `c`, `b` and the total error; `incEval_sound` is the statement.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset Complex CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

/-- Real coefficient `c_m` of the incident model (`L = Log(-e)`). -/
noncomputable def cinc (a : ℕ → ℚ) (d : ℕ) (e : CQ) (L : ℂ) (m : ℕ) : ℝ :=
  ((PBc a d CQ.zero e m).toC * L + (Rc a d CQ.zero e m).toC
    + (jetc (PAc a d CQ.zero e) e m).toC).re

theorem incA_model (a : ℕ → ℚ) (d n : ℕ) (hn : d + 2 ≤ n) (A B dd : CQ) (h rq : ℚ)
    (hh : 0 ≤ h) (hv : (CQ.sub B A).nsq ≠ 0) (he0 : (eof A B dd).nsq ≠ 0)
    (hr0 : 0 ≤ rq) (hr1 : rq < 1) (hq : (eof A B dd).nsq * h ^ 2 ≤ rq ^ 2)
    (L : ℂ) (hL : L = Complex.log (-(eof A B dd).toC))
    (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ (h : ℝ)) :
    |(∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), (a k : ℝ) * t ^ k) *
        Real.log ‖(A.toC + (s : ℂ) * dd.toC) - (A.toC + (t : ℂ) * (B.toC - A.toC))‖)
      - ((massQ a d : ℝ) * Real.log ‖B.toC - A.toC‖
        + ∑ m ∈ range n, cinc a d (eof A B dd) L m * s ^ m
        + Real.log s * ∑ m ∈ range n, ((PBc a d CQ.zero (eof A B dd) m).re : ℝ) * s ^ m)|
    ≤ (jbQ (PAc a d CQ.zero (eof A B dd)) n rq h : ℝ) := by
  set e := eof A B dd with hedef
  have hBA : B.toC - A.toC ≠ 0 := by rw [← CQ.toC_sub]; exact CQ.toC_ne_zero hv
  have he : e.toC = dd.toC / (B.toC - A.toC) := by
    rw [hedef]; unfold eof; rw [CQ.toC_div _ _ hv, CQ.toC_sub]
  have hζ : ((A.toC + (s : ℂ) * dd.toC) - A.toC) / (B.toC - A.toC)
      = CQ.zero.toC + e.toC * (s : ℂ) := by
    rw [he, CQ.toC_zero]; field_simp; ring
  have hI := potential_closed a d A.toC B.toC (A.toC + (s : ℂ) * dd.toC) hBA
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hn1 := norm_le_of_nsq hh hr0 hq
  have hr1R : (rq : ℝ) < 1 := by exact_mod_cast hr1
  have hsC : ‖(s : ℂ)‖ ≤ (h : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs
  have hlog1 : Complex.log (1 - (CQ.zero.toC + e.toC * (s : ℂ)))
      = Complex.log (1 - e.toC * (s : ℂ)) := by
    rw [CQ.toC_zero, zero_add]
  have hPBlog : PBf a d (CQ.zero.toC + e.toC * (s : ℂ)) *
        Complex.log (-(CQ.zero.toC + e.toC * (s : ℂ)))
      = PBf a d (CQ.zero.toC + e.toC * (s : ℂ)) * (((Real.log s : ℝ) : ℂ) + L) := by
    rcases hs0.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp [PBf, CQ.toC_zero]
    · have hlogs : Complex.log (-(CQ.zero.toC + e.toC * (s : ℂ))) = ((Real.log s : ℝ) : ℂ) + L := by
        have : -(CQ.zero.toC + e.toC * (s : ℂ)) = (s : ℂ) * (-e.toC) := by
          rw [CQ.toC_zero]; ring
        rw [this, hL]
        exact Complex.log_ofReal_mul hpos (neg_ne_zero.2 (CQ.toC_ne_zero he0))
      rw [hlogs]
  rw [hI, hζ, hlog1, hPBlog, ← PA_expand a d CQ.zero e (s : ℂ) n hn,
    ← PB_expand a d CQ.zero e (s : ℂ) n hn, ← R_expand a d CQ.zero e (s : ℂ) n (by omega)]
  set PAf : ℕ → ℂ := fun j => (PAc a d CQ.zero e j).toC with hPAf
  set LA := Complex.log (1 - e.toC * (s : ℂ)) with hLA
  have hJA : jet n PAf e.toC (s : ℂ) = ∑ m ∈ range n, (jetc (PAc a d CQ.zero e) e m).toC * (s : ℂ) ^ m :=
    jet_expand (PAc a d CQ.zero e) e (s : ℂ) n
  set PAs := ∑ m ∈ range n, PAf m * (s : ℂ) ^ m with hPAs
  set PBs := ∑ m ∈ range n, (PBc a d CQ.zero e m).toC * (s : ℂ) ^ m with hPBs
  set Rs := ∑ m ∈ range n, (Rc a d CQ.zero e m).toC * (s : ℂ) ^ m with hRs
  have hcm : ∑ m ∈ range n, cinc a d e L m * s ^ m
      = (PBs * L + Rs + jet n PAf e.toC (s : ℂ)).re := by
    rw [hJA]
    have h1 : ∀ m ∈ range n, cinc a d e L m * s ^ m
        = (((PBc a d CQ.zero e m).toC * L + (Rc a d CQ.zero e m).toC
          + (jetc (PAc a d CQ.zero e) e m).toC) * (s : ℂ) ^ m).re := by
      intro m _
      unfold cinc
      rw [show (s : ℂ) ^ m = ((s ^ m : ℝ) : ℂ) by push_cast; rfl, Complex.re_mul_ofReal]
    rw [Finset.sum_congr rfl h1, ← Complex.re_sum]
    congr 1
    have h2 : ∀ m ∈ range n, ((PBc a d CQ.zero e m).toC * L + (Rc a d CQ.zero e m).toC
          + (jetc (PAc a d CQ.zero e) e m).toC) * (s : ℂ) ^ m
        = (PBc a d CQ.zero e m).toC * (s : ℂ) ^ m * L + (Rc a d CQ.zero e m).toC * (s : ℂ) ^ m
          + (jetc (PAc a d CQ.zero e) e m).toC * (s : ℂ) ^ m := by
      intro m _; ring
    rw [Finset.sum_congr rfl h2]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  have hlg : Real.log s * ∑ m ∈ range n, ((PBc a d CQ.zero e m).re : ℝ) * s ^ m
      = (((Real.log s : ℝ) : ℂ) * PBs).re := by
    rw [Complex.re_ofReal_mul, hPBs, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (s : ℂ) ^ m = ((s ^ m : ℝ) : ℂ) by push_cast; rfl, Complex.re_mul_ofReal]
    rfl
  rw [hcm, hlg]
  have hrem := norm_jet_remainder_le n PAf hsC (q := e.toC) (by linarith)
  have hbd := jetBound_le_jbQ (q := e.toC) (PAc a d CQ.zero e) n hh hn1 hr1
  have hdiff : ((massQ a d : ℝ) * Real.log ‖B.toC - A.toC‖
        + (PAs * LA + PBs * (((Real.log s : ℝ) : ℂ) + L) + Rs).re)
      - ((massQ a d : ℝ) * Real.log ‖B.toC - A.toC‖ + (PBs * L + Rs + jet n PAf e.toC (s : ℂ)).re
        + (((Real.log s : ℝ) : ℂ) * PBs).re)
      = (PAs * LA - jet n PAf e.toC (s : ℂ)).re := by
    have hz : PAs * LA - jet n PAf e.toC (s : ℂ) =
        (PAs * LA + PBs * (((Real.log s : ℝ) : ℂ) + L) + Rs)
          - (PBs * L + Rs + jet n PAf e.toC (s : ℂ)) - (((Real.log s : ℝ) : ℂ) * PBs) := by ring
    rw [hz, Complex.sub_re, Complex.sub_re]; ring
  rw [hdiff]
  refine (Complex.abs_re_le_norm _).trans (hrem.trans ?_)
  exact_mod_cast hbd

end CatalanCore.Uniform.Decay.Breakpoint
