module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a0
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a1
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a2
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a3

@[expose] public section

/-!
# G5 shiftG, leaf Y1a: column sup of the first population at `γ = 11/50`

`2 T(dv24, s) + (11/50) log (1 + 3 s/4) ≤ 14224759/10^8` on `[0,1]`, from the four quarter checks
(`ShiftGLeafY1a0 … 3`) by `leafY_quarters` (the proof of `ShiftGLeaf.leafY` with the cover of `[0,1]` by the
cells `[i/4, (i+1)/4]`).  True sup 0.1422475608 (at s = 0.075321).
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf OAI.InternalCatalan

noncomputable section

theorem quarters_nonneg {p : List ℤ} {f : ℕ} (h0 : checkZ p f 0 2 = true) (h1 : checkZ p f 1 2 = true)
    (h2 : checkZ p f 2 2 = true) (h3 : checkZ p f 3 2 = true) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ evalZ p s := by
  rcases le_or_gt s (1 / 4) with c0 | c0
  · exact checkZ_sound h0 (w := s) (by simpa using hs.1) (by norm_num; linarith)
  rcases le_or_gt s (1 / 2) with c1 | c1
  · exact checkZ_sound h1 (w := s) (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt s (3 / 4) with c2 | c2
  · exact checkZ_sound h2 (w := s) (by norm_num; linarith) (by norm_num; linarith)
  · exact checkZ_sound h3 (w := s) (by norm_num; linarith) (by norm_num; linarith [hs.2])

/-- **The column sup** `hY`: `2 T(dv, s) + (gn/gd) log (1 + 3 s / 4) ≤ yn / yd` on `[0,1]`. -/
theorem leafY_quarters {Λ : ℤ} (hΛ : 0 < Λ) (dv : List ℤ) (hdv : ∀ k, k < dv.length → ((k : ℤ) + 1) ∣ Λ)
    (gn gd yn yd : ℤ) (hgn : 0 ≤ gn) (hgd : 0 < gd) (hyd : 0 < yd) {f : ℕ}
    (h0 : checkZ (addL (combZ (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd)
        (wts (-2 * 4 ^ 65 * L64 * gd * yd) Λ dv) [])
        (smulL (-(gn * 2 ^ 24 * Λ * yd)) (0 :: logW))) f 0 2 = true)
    (h1 : checkZ (addL (combZ (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd)
        (wts (-2 * 4 ^ 65 * L64 * gd * yd) Λ dv) [])
        (smulL (-(gn * 2 ^ 24 * Λ * yd)) (0 :: logW))) f 1 2 = true)
    (h2 : checkZ (addL (combZ (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd)
        (wts (-2 * 4 ^ 65 * L64 * gd * yd) Λ dv) [])
        (smulL (-(gn * 2 ^ 24 * Λ * yd)) (0 :: logW))) f 2 2 = true)
    (h3 : checkZ (addL (combZ (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd)
        (wts (-2 * 4 ^ 65 * L64 * gd * yd) Λ dv) [])
        (smulL (-(gn * 2 ^ 24 * Λ * yd)) (0 :: logW))) f 3 2 = true) :
    ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv (2 ^ 24)) s +
      ((gn : ℝ) / gd) * Real.log (1 + 3 / 4 * s) ≤ (yn : ℝ) / yd := by
  intro s hs
  have hw := quarters_nonneg h0 h1 h2 h3 hs
  rw [evalZ_addL, evalZ_combZ, evalZ_smulL, evalZ_logW, wts_length,
    trialT_wts (-2 * 4 ^ 65 * L64 * gd * yd) (2 ^ 24) (by norm_num) dv hdv] at hw
  have hlog := log_le_logW hs.1 hs.2
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hgd' : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hyd' : (0 : ℝ) < yd := by exact_mod_cast hyd
  have hgn' : (0 : ℝ) ≤ gn := by exact_mod_cast hgn
  have hL : (0 : ℝ) < L64 := by unfold L64; norm_num
  have hP : (0 : ℝ) < 4 ^ 65 * L64 := by positivity
  simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero] at hw
  set Tt := barrierTrialT (trialSeqOf dv (2 ^ 24)) s with hT
  set Sl := ∑ i ∈ Finset.range 65, (logW.getD i 0 : ℝ) * s ^ (i + 1) with hSl
  push_cast at hw
  rw [le_div_iff₀ hP] at hlog
  have hM : (0 : ℝ) < 2 ^ 24 * Λ * (4 ^ 65 * L64) * gd * yd := by positivity
  have hgl : (gn : ℝ) * ((4 : ℝ) ^ 65 * L64) * Real.log (1 + 3 / 4 * s) ≤ gn * Sl := by
    have := mul_le_mul_of_nonneg_left hlog hgn'
    linarith
  have hgd0 : (gd : ℝ) ≠ 0 := hgd'.ne'
  have hyd0 : (yd : ℝ) ≠ 0 := hyd'.ne'
  have key : 0 ≤ (2 ^ 24 * Λ * (4 ^ 65 * L64) * gd * yd) * ((yn : ℝ) / yd - (2 * Tt +
      (gn / gd) * Real.log (1 + 3 / 4 * s))) := by
    have e : (2 ^ 24 * Λ * (4 ^ 65 * L64) * gd * yd) * ((yn : ℝ) / yd - (2 * Tt +
        (gn / gd) * Real.log (1 + 3 / 4 * s))) =
        (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd + (-2 * 4 ^ 65 * L64 * gd * yd) * Λ * 2 ^ 24 * Tt +
          (-(gn * 2 ^ 24 * Λ * yd)) * Sl) +
        (2 ^ 24 * Λ * yd) * (gn * Sl - gn * (4 ^ 65 * L64) * Real.log (1 + 3 / 4 * s)) := by
      field_simp
      ring
    rw [e]
    have h2 : 0 ≤ (2 ^ 24 * (Λ : ℝ) * yd) * (gn * Sl - gn * (4 ^ 65 * L64) *
        Real.log (1 + 3 / 4 * s)) := mul_nonneg (by positivity) (by linarith)
    linarith [hw]
  have := nonneg_of_mul_nonneg_right key hM
  linarith



theorem div : divOK 5354228880 24 = true := by decide +kernel

theorem dv_div (k : ℕ) (hk : k < dv24.length) : ((k : ℤ) + 1) ∣ 5354228880 := by
  rw [len_dv24] at hk; exact divOK_spec div hk

/-- `γ = 11/50`, true sup 0.1422475608 (at s = 0.075321). -/
theorem Y1_11_50_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv24 (2 ^ 24)) s +
    (11 / 50 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (14224759 : ℝ) / 10 ^ 8 := by
  have h := leafY_quarters (Λ := 5354228880) (by norm_num) dv24 dv_div 11 50 14224759 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num)
    ShiftGLeafY1a0.Y1_11_50_q0_check ShiftGLeafY1a1.Y1_11_50_q1_check
    ShiftGLeafY1a2.Y1_11_50_q2_check ShiftGLeafY1a3.Y1_11_50_q3_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a.Y1_11_50_leaf
