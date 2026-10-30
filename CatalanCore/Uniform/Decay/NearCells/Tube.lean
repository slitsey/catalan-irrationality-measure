module

public import CatalanCore.Uniform.Decay.NearCells.Agg
public import CatalanCore.Uniform.Decay.Cells.Facts
public import CatalanCore.Uniform.Decay.Assembly.SegmentModulus
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
set_option Elab.async false

/-!
# The transverse perturbation and the full cell inequality (lane D, package D6b)

`modOk` / `modQ`: D5a's `segment_log_modulus` with `|log W|` and `log(1 + L/(3W))` bounded by
checked binary exponents `eW`, `eP` (`log 2 < 7/10`).
`cell_sound`: for `|s| ≤ h`, `|δ| ≤ W`,
`lo - F - ML + cπ · y⁺ ≤ - ∑ w_P Φ_P(zc + s dd + δ) + (1-ε) π |Im (zc + s dd + δ)|`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.Assembly

/-- Per-piece modulus data check. -/
def modOk (P : WP) (Rtwo W : ℚ) (eW eP : ℕ) : Bool :=
  decide (0 < P.Lq) && decide (P.Lq ^ 2 ≤ (CQ.sub P.B P.A).nsq) &&
  decide ((CQ.sub P.B P.A).nsq ≤ Rtwo ^ 2) && decide (0 ≤ Rtwo) && bernOkK P.a 0 P.M &&
  decide (P.a ≠ []) && decide (0 < W) && decide (W ≤ 1 / 4) && decide (1 ≤ W * 2 ^ eW) &&
  decide (1 + Rtwo / (3 * W) ≤ 2 ^ eP)

/-- Per-piece modulus bound. -/
def modQ (P : WP) (W : ℚ) (eW eP : ℕ) : ℚ :=
  P.M / P.Lq * W * (17 + 14 * (7 / 10) * eW + 3 * (7 / 10) * eP)

def modSum (Rtwo W : ℚ) (eW eP : ℕ) : List WP → ℚ
  | [] => 0
  | P :: ps => |P.w| * modQ P W eW eP + modSum Rtwo W eW eP ps

def modAll (Rtwo W : ℚ) (eW eP : ℕ) (ps : List WP) : Bool :=
  ps.all fun P => modOk P Rtwo W eW eP

theorem log_two_le : Real.log 2 ≤ 7 / 10 := by
  have := Real.log_two_lt_d9; norm_num at this; linarith

theorem PhiW_modulus {P : WP} {Rtwo W : ℚ} {eW eP : ℕ} (h : modOk P Rtwo W eW eP = true)
    {z z' : ℂ} (hzz : ‖z - z'‖ ≤ (W : ℝ)) :
    |PhiW P z - PhiW P z'| ≤ (modQ P W eW eP : ℝ) := by
  simp only [modOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hLq, hLv⟩, hvR⟩, hR0⟩, hbern⟩, hne⟩, hW0⟩, hW4⟩, hW2⟩, hP2⟩ := h
  have hnsq : (CQ.sub P.B P.A).nsq ≠ 0 := by
    intro h0; rw [h0] at hLv; nlinarith [sq_nonneg P.Lq]
  have hvne : (CQ.sub P.B P.A).toC ≠ 0 := CQ.toC_ne_zero hnsq
  have hvn : ‖P.B.toC - P.A.toC‖ ^ 2 = (((CQ.sub P.B P.A).nsq : ℚ) : ℝ) := by
    rw [← CQ.toC_sub, Complex.sq_norm, ← CQ.nsq_cast]
  have hvpos : 0 < ‖P.B.toC - P.A.toC‖ := by
    rw [← CQ.toC_sub]; exact norm_pos_iff.2 hvne
  have hLqR : (0 : ℝ) < P.Lq := by exact_mod_cast hLq
  have hLle : (P.Lq : ℝ) ≤ ‖P.B.toC - P.A.toC‖ := by
    have : (P.Lq : ℝ) ^ 2 ≤ ‖P.B.toC - P.A.toC‖ ^ 2 := by rw [hvn]; exact_mod_cast hLv
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg (P.B.toC - P.A.toC)]
  have hRle : ‖P.B.toC - P.A.toC‖ ≤ (Rtwo : ℝ) := by
    have h1 : ‖P.B.toC - P.A.toC‖ ^ 2 ≤ (Rtwo : ℝ) ^ 2 := by rw [hvn]; exact_mod_cast hvR
    have hR0' : (0 : ℝ) ≤ Rtwo := by exact_mod_cast hR0
    nlinarith [norm_nonneg (P.B.toC - P.A.toC)]
  have hAB : P.A.toC ≠ P.B.toC := by
    intro h0; apply hvne; rw [CQ.toC_sub, h0, sub_self]
  -- density
  have hfc : Continuous (ratPoly P.a) := continuous_ratPoly P.a
  have hfb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |ratPoly P.a t| ≤ (P.M : ℝ) := by
    intro t ht
    have := ratPoly_bounds hne hbern ht.1 ht.2
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ ratPoly P.a t := by simpa using this.1
      have h0 : (0 : ℝ) ≤ P.M := by
        have := ratPoly_bounds hne hbern (le_refl (0 : ℝ)) zero_le_one
        simpa using this.1.trans this.2
      linarith
    · exact this.2
  have hM0 : (0 : ℝ) ≤ P.M := (abs_nonneg _).trans (hfb 0 ⟨le_rfl, zero_le_one⟩)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW4R : (W : ℝ) ≤ 1 / 4 := by
    have := (Rat.cast_le (K := ℝ)).2 hW4; push_cast at this; exact this
  have hmod := segment_log_modulus hAB hfc hfb hWR hW4R hzz
  -- PhiW = - (integral of f * (-log))
  have hPhi : ∀ y : ℂ, PhiW P y = -∫ t in (0 : ℝ)..1, ratPoly P.a t *
      (-Real.log ‖y - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖) := by
    intro y
    unfold PhiW
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ratPoly]; ring
  rw [hPhi z, hPhi z', neg_sub_neg, abs_sub_comm]
  refine hmod.trans ?_
  -- numeric bound
  have hlogW : |Real.log W| ≤ eW * (7 / 10) := by
    have h1 : (1 : ℝ) ≤ W * 2 ^ eW := by exact_mod_cast hW2
    have hl : Real.log W < 0 := Real.log_neg hWR (by linarith)
    rw [abs_of_neg hl]
    have : Real.log ((2 : ℝ) ^ eW)⁻¹ ≤ Real.log W := by
      apply Real.log_le_log (by positivity)
      rw [← one_div, div_le_iff₀ (by positivity)]; exact h1
    rw [Real.log_inv, Real.log_pow] at this
    nlinarith [log_two_le, Nat.cast_nonneg (α := ℝ) eW, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlogP : Real.log (1 + ‖P.B.toC - P.A.toC‖ / (3 * W)) ≤ eP * (7 / 10) := by
    have h1 : (1 : ℝ) + ‖P.B.toC - P.A.toC‖ / (3 * W) ≤ 2 ^ eP := by
      have : (1 : ℝ) + Rtwo / (3 * W) ≤ 2 ^ eP := by exact_mod_cast hP2
      have h2 : ‖P.B.toC - P.A.toC‖ / (3 * (W : ℝ)) ≤ Rtwo / (3 * W) :=
        div_le_div_of_nonneg_right hRle (by positivity)
      linarith
    have hpos : 0 < (1 : ℝ) + ‖P.B.toC - P.A.toC‖ / (3 * W) := by positivity
    calc Real.log (1 + ‖P.B.toC - P.A.toC‖ / (3 * W)) ≤ Real.log ((2 : ℝ) ^ eP) :=
          Real.log_le_log hpos h1
      _ = eP * Real.log 2 := Real.log_pow _ _
      _ ≤ eP * (7 / 10) := mul_le_mul_of_nonneg_left log_two_le (Nat.cast_nonneg _)
  have hMd : (P.M : ℝ) / ‖P.B.toC - P.A.toC‖ ≤ (P.M : ℝ) / P.Lq :=
    div_le_div_of_nonneg_left hM0 hLqR hLle
  unfold modQ
  push_cast
  have hin : (17 + 14 * |Real.log W| + 3 * Real.log (1 + ‖P.B.toC - P.A.toC‖ / (3 * W)))
      ≤ 17 + 14 * (7 / 10) * eW + 3 * (7 / 10) * eP := by nlinarith
  calc (P.M : ℝ) / ‖P.B.toC - P.A.toC‖ * (W * (17 + 14 * |Real.log W|
          + 3 * Real.log (1 + ‖P.B.toC - P.A.toC‖ / (3 * W))))
      ≤ (P.M : ℝ) / P.Lq * (W * (17 + 14 * (7 / 10) * eW + 3 * (7 / 10) * eP)) := by
        have hlognn : 0 ≤ Real.log (1 + ‖P.B.toC - P.A.toC‖ / (3 * W)) :=
          Real.log_nonneg (by have : 0 ≤ ‖P.B.toC - P.A.toC‖ / (3 * (W : ℝ)) := by positivity
                              linarith)
        apply mul_le_mul hMd (mul_le_mul_of_nonneg_left hin hWR.le)
          (mul_nonneg hWR.le (by nlinarith [abs_nonneg (Real.log W)]))
          (div_nonneg hM0 hLqR.le)
    _ = _ := by ring

end CatalanCore.Uniform.Decay.NearCells
