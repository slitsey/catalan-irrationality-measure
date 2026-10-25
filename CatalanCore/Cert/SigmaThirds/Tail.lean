module

public import CatalanCore.Cert.SigmaThirds.Symm
public import CatalanCore.Cert.SigmaThirds.TailGeometry

@[expose] public section

/-!
# Broad-support tail bound for the thirds witness

Atoms lie in `[-1,1] × [-3/2,3/2]`, hence their norms are at most2.
For `u ≥ 3/2`, the squared regularised point distance is at most `25 u²`.
The logarithmic tail estimate uses `log25 = 2log5 ≤8`; the positive field is at least11.
This is a private adapted template; it still requires Lean verification for the chosen witness.
-/

open Real

namespace CatalanCore.Cert.SigmaThirds

open _root_.CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

def posOK (k : ℕ) : Bool :=
  decide (-(2 ^ 40 : ℤ) ≤ (ptAt k).1) && decide ((ptAt k).1 ≤ 2 ^ 40) &&
    decide (2 * (ptAt k).2.1 ≤ 3 * 2 ^ 40) && decide (-(3 * 2 ^ 40 : ℤ) ≤ 2 * (ptAt k).2.1)

theorem pos_c0 : (List.range 50).all (fun i => posOK (50 * 0 + i)) = true := by decide +kernel

theorem pos_c1 : (List.range 50).all (fun i => posOK (50 * 1 + i)) = true := by decide +kernel

theorem pos_c2 : (List.range 50).all (fun i => posOK (50 * 2 + i)) = true := by decide +kernel

theorem pos_c3 : (List.range 50).all (fun i => posOK (50 * 3 + i)) = true := by decide +kernel

theorem pos_c4 : (List.range 50).all (fun i => posOK (50 * 4 + i)) = true := by decide +kernel

theorem pos_c5 : (List.range 50).all (fun i => posOK (50 * 5 + i)) = true := by decide +kernel

theorem pos_c6 : (List.range 50).all (fun i => posOK (50 * 6 + i)) = true := by decide +kernel

theorem pos_c7 : (List.range 50).all (fun i => posOK (50 * 7 + i)) = true := by decide +kernel

theorem pos_c8 : (List.range 50).all (fun i => posOK (50 * 8 + i)) = true := by decide +kernel

theorem pos_c9 : (List.range 50).all (fun i => posOK (50 * 9 + i)) = true := by decide +kernel

theorem pos_c10 : (List.range 50).all (fun i => posOK (50 * 10 + i)) = true := by decide +kernel

theorem pos_c11 : (List.range 50).all (fun i => posOK (50 * 11 + i)) = true := by decide +kernel

theorem pos_c12 : (List.range 50).all (fun i => posOK (50 * 12 + i)) = true := by decide +kernel

theorem pos_c13 : (List.range 50).all (fun i => posOK (50 * 13 + i)) = true := by decide +kernel

theorem pos_c14 : (List.range 50).all (fun i => posOK (50 * 14 + i)) = true := by decide +kernel

theorem pos_c15 : (List.range 50).all (fun i => posOK (50 * 15 + i)) = true := by decide +kernel

theorem pos_c16 : (List.range 50).all (fun i => posOK (50 * 16 + i)) = true := by decide +kernel

theorem pos_c17 : (List.range 50).all (fun i => posOK (50 * 17 + i)) = true := by decide +kernel

theorem pos_c18 : (List.range 50).all (fun i => posOK (50 * 18 + i)) = true := by decide +kernel

theorem pos_c19 : (List.range 50).all (fun i => posOK (50 * 19 + i)) = true := by decide +kernel

theorem pos_c20 : (List.range 50).all (fun i => posOK (50 * 20 + i)) = true := by decide +kernel

theorem pos_c21 : (List.range 50).all (fun i => posOK (50 * 21 + i)) = true := by decide +kernel

theorem pos_c22 : (List.range 50).all (fun i => posOK (50 * 22 + i)) = true := by decide +kernel

theorem pos_c23 : (List.range 50).all (fun i => posOK (50 * 23 + i)) = true := by decide +kernel

theorem pos_c24 : (List.range 50).all (fun i => posOK (50 * 24 + i)) = true := by decide +kernel

theorem pos_c25 : (List.range 50).all (fun i => posOK (50 * 25 + i)) = true := by decide +kernel

theorem pos_c26 : (List.range 50).all (fun i => posOK (50 * 26 + i)) = true := by decide +kernel

theorem pos_c27 : (List.range 50).all (fun i => posOK (50 * 27 + i)) = true := by decide +kernel

theorem pos_c28 : (List.range 50).all (fun i => posOK (50 * 28 + i)) = true := by decide +kernel

theorem pos_c29 : (List.range 50).all (fun i => posOK (50 * 29 + i)) = true := by decide +kernel

theorem pos_c30 : (List.range 50).all (fun i => posOK (50 * 30 + i)) = true := by decide +kernel

theorem pos_c31 : (List.range 50).all (fun i => posOK (50 * 31 + i)) = true := by decide +kernel

theorem pos_c32 : (List.range 50).all (fun i => posOK (50 * 32 + i)) = true := by decide +kernel

theorem pos_c33 : (List.range 50).all (fun i => posOK (50 * 33 + i)) = true := by decide +kernel

theorem pos_c34 : (List.range 50).all (fun i => posOK (50 * 34 + i)) = true := by decide +kernel

theorem pos_c35 : (List.range 50).all (fun i => posOK (50 * 35 + i)) = true := by decide +kernel

theorem pos_c36 : (List.range 50).all (fun i => posOK (50 * 36 + i)) = true := by decide +kernel

theorem pos_c37 : (List.range 50).all (fun i => posOK (50 * 37 + i)) = true := by decide +kernel

theorem pos_c38 : (List.range 50).all (fun i => posOK (50 * 38 + i)) = true := by decide +kernel

theorem pos_c39 : (List.range 50).all (fun i => posOK (50 * 39 + i)) = true := by decide +kernel

theorem pos_c40 : (List.range 50).all (fun i => posOK (50 * 40 + i)) = true := by decide +kernel

theorem pos_c41 : (List.range 50).all (fun i => posOK (50 * 41 + i)) = true := by decide +kernel

theorem pos_c42 : (List.range 50).all (fun i => posOK (50 * 42 + i)) = true := by decide +kernel

theorem pos_c43 : (List.range 50).all (fun i => posOK (50 * 43 + i)) = true := by decide +kernel

theorem pos_c44 : (List.range 50).all (fun i => posOK (50 * 44 + i)) = true := by decide +kernel

theorem pos_c45 : (List.range 50).all (fun i => posOK (50 * 45 + i)) = true := by decide +kernel

theorem pos_c46 : (List.range 50).all (fun i => posOK (50 * 46 + i)) = true := by decide +kernel

theorem pos_c47 : (List.range 50).all (fun i => posOK (50 * 47 + i)) = true := by decide +kernel

theorem pos_c48 : (List.range 50).all (fun i => posOK (50 * 48 + i)) = true := by decide +kernel

theorem pos_c49 : (List.range 50).all (fun i => posOK (50 * 49 + i)) = true := by decide +kernel

theorem pos_c50 : (List.range 50).all (fun i => posOK (50 * 50 + i)) = true := by decide +kernel

theorem pos_c51 : (List.range 50).all (fun i => posOK (50 * 51 + i)) = true := by decide +kernel

theorem pos_c52 : (List.range 50).all (fun i => posOK (50 * 52 + i)) = true := by decide +kernel

theorem pos_c53 : (List.range 50).all (fun i => posOK (50 * 53 + i)) = true := by decide +kernel

theorem pos_c54 : (List.range 50).all (fun i => posOK (50 * 54 + i)) = true := by decide +kernel

theorem pos_c55 : (List.range 50).all (fun i => posOK (50 * 55 + i)) = true := by decide +kernel

theorem pos_c56 : (List.range 50).all (fun i => posOK (50 * 56 + i)) = true := by decide +kernel

theorem pos_c57 : (List.range 50).all (fun i => posOK (50 * 57 + i)) = true := by decide +kernel

theorem pos_c58 : (List.range 50).all (fun i => posOK (50 * 58 + i)) = true := by decide +kernel

theorem pos_check : (List.range 2950).all posOK = true :=
  all_chunks posOK 59 50 (by
    intro m hm
    interval_cases m
    exacts [pos_c0, pos_c1, pos_c2, pos_c3, pos_c4, pos_c5, pos_c6, pos_c7, pos_c8, pos_c9, pos_c10, pos_c11, pos_c12, pos_c13, pos_c14, pos_c15, pos_c16, pos_c17, pos_c18, pos_c19, pos_c20, pos_c21, pos_c22, pos_c23, pos_c24, pos_c25, pos_c26, pos_c27, pos_c28, pos_c29, pos_c30, pos_c31, pos_c32, pos_c33, pos_c34, pos_c35, pos_c36, pos_c37, pos_c38, pos_c39, pos_c40, pos_c41, pos_c42, pos_c43, pos_c44, pos_c45, pos_c46, pos_c47, pos_c48, pos_c49, pos_c50, pos_c51, pos_c52, pos_c53, pos_c54, pos_c55, pos_c56, pos_c57, pos_c58])

lemma pos_bounds (k : Fin 2950) :
    -(1 : ℝ) ≤ (cH k).re ∧ (cH k).re ≤ 1 ∧ -(3 / 2 : ℝ) ≤ (cH k).im ∧ (cH k).im ≤ 3 / 2 := by
  have h := List.all_eq_true.mp pos_check k (List.mem_range.mpr k.2)
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have r1 : (-(2 ^ 40 : ℝ)) ≤ ((ptAt k).1 : ℝ) := by exact_mod_cast h1
  have r2 : ((ptAt k).1 : ℝ) ≤ 2 ^ 40 := by exact_mod_cast h2
  have r3 : 2 * ((ptAt k).2.1 : ℝ) ≤ 3 * 2 ^ 40 := by exact_mod_cast h3
  have r4 : (-(3 * 2 ^ 40 : ℝ)) ≤ 2 * ((ptAt k).2.1 : ℝ) := by exact_mod_cast h4
  simp only [cH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem cH_norm (k : Fin 2950) : ‖cH k‖ ≤ 2 := by
  obtain ⟨a, b, c, d⟩ := pos_bounds k
  exact CatalanCore.Cert.SigmaThirds.rectangle_norm_le_two (cH k).re (cH k).im a b c d

theorem tail_pt (c : ℂ) (h1 : -(1 : ℝ) ≤ c.re) (h2 : c.re ≤ 1) (h3 : -(3 / 2 : ℝ) ≤ c.im)
    (h4 : c.im ≤ 3 / 2) (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    ‖(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) - c‖ ^ 2 + (1 / 4096 : ℝ) ^ 2 ≤ 25 * u ^ 2 := by
  have e : ‖(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) - c‖ ^ 2
      = (-(7 / 50 : ℝ) + δ - u - c.re) ^ 2 + (5 / 2 * u - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [e]
  exact CatalanCore.Cert.SigmaThirds.tail_distance_sq_le c.re c.im u δ h1 h2 h3 h4 hu hδ

theorem Usig_tail_lb (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    -(9 / 16) * Real.log (25 * u ^ 2) ≤
      CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ := by
  have hu0 : 0 < u := by linarith
  unfold CatalanLambda.Decay.Usig
  have h1 : ∀ k : Fin 2950, mH k * (-(1 / 2) * Real.log (25 * u ^ 2)) ≤
      mH k * CatalanLambda.Decay.krho (1 / 4096 : ℝ) ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ (cH k) := by
    intro k
    have hm : 0 ≤ mH k := by unfold mH; positivity
    apply mul_le_mul_of_nonneg_left _ hm
    unfold CatalanLambda.Decay.krho
    obtain ⟨b1, b2, b3, b4⟩ := pos_bounds k
    have hp : 0 < ‖(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) - cH k‖ ^ 2 + (1 / 4096 : ℝ) ^ 2 := by positivity
    have := Real.log_le_log hp (tail_pt (cH k) b1 b2 b3 b4 u δ hu hδ)
    linarith
  calc -(9 / 16) * Real.log (25 * u ^ 2) = ∑ k, mH k * (-(1 / 2) * Real.log (25 * u ^ 2)) := by
        rw [← Finset.sum_mul, mH_sum]; ring
    _ ≤ _ := Finset.sum_le_sum (fun k _ => h1 k)

theorem Utau_tail_ub (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) :
    CatalanLambda.Decay.Utau (⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) ≤ -Real.log (5 / 2 * u) := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ with hz
  unfold CatalanLambda.Decay.Utau
  have hge : ∀ t : ℝ, 5 / 2 * u ≤ ‖z - (t : ℂ)‖ := by
    intro t
    have h := Complex.abs_im_le_norm (z - (t : ℂ))
    have e : (z - (t : ℂ)).im = 5 / 2 * u := by simp [hz]
    rw [e, abs_of_pos (by positivity)] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => -Real.log ‖z - (t : ℂ)‖) (Set.uIcc 0 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · fun_prop
    · intro t _
      have := hge t
      have : 0 < ‖z - (t : ℂ)‖ := lt_of_lt_of_le (by positivity) this
      exact this.ne'
  have hmono := intervalIntegral.integral_mono_on (a := 0) (b := 1) zero_le_one
    hcont.intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -Real.log (5 / 2 * u)) MeasureTheory.volume 0 1)
    (fun t _ => by
      have := Real.log_le_log (by positivity) (hge t)
      linarith)
  simpa using hmono

theorem Uex_tail_ub (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) :
    CatalanCore.Decay.Uex (2 * (1 / 8 : ℝ)) (⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ)
      ≤ -(1 / 8) * Real.log (5 / 2 * u) := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ with hz
  unfold CatalanCore.Decay.Uex
  have hge : ∀ t : ℝ, 5 / 2 * u ≤ ‖z - (t : ℂ)‖ := by
    intro t
    have h := Complex.abs_im_le_norm (z - (t : ℂ))
    have e : (z - (t : ℂ)).im = 5 / 2 * u := by simp [hz]
    rw [e, abs_of_pos (by positivity)] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => CatalanLambda.Decay.elog z (t : ℂ)) (Set.uIcc 1 (1 + 2 * (1 / 8))) := by
    unfold CatalanLambda.Decay.elog
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · fun_prop
    · intro t _
      have := hge t
      have : 0 < ‖z - (t : ℂ)‖ := lt_of_lt_of_le (by positivity) this
      exact this.ne'
  have hmono := intervalIntegral.integral_mono_on (a := 1) (b := 1 + 2 * (1 / 8)) (by norm_num)
    hcont.intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -Real.log (5 / 2 * u)) MeasureTheory.volume 1 (1 + 2 * (1 / 8)))
    (fun t _ => by
      unfold CatalanLambda.Decay.elog
      have := Real.log_le_log (by positivity) (hge t)
      linarith)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have e : (1 + 2 * (1 / 8 : ℝ) - 1) = 1 / 4 := by norm_num
  rw [e] at hmono
  linarith

theorem tail_hyb (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    (103161 / 50000 : ℝ) ≤ gHyb ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ := by
  have hu0 : 0 < u := by linarith
  have h1 := Usig_tail_lb u δ hu hδ
  have h2 := Utau_tail_ub u δ hu
  have h3 := Uex_tail_ub u δ hu
  have ldist : Real.log (25 * u ^ 2) = Real.log 25 + 2 * Real.log u := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have lray : Real.log (5 / 2 * u) = Real.log (5 / 2) + Real.log u :=
    Real.log_mul (by norm_num) hu0.ne'
  have hdist : Real.log (25 : ℝ) ≤ 8 := by
    have h5 : Real.log (5 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
      linarith
    have e : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e, Real.log_pow]
    norm_num
    linarith
  have hray : 0 ≤ Real.log (5 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  rw [gHyb_eq]
  have him : |(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ).im| = 5 / 2 * u :=
    abs_of_pos (by show 0 < 5 / 2 * u; positivity)
  rw [him]
  unfold CatalanCore.Decay.Unu
  have hf : (1 - (1 / 1000 : ℝ)) * Real.pi * (5 / 2 * u) ≥ 11 := by nlinarith
  rw [ldist] at h1
  rw [lray] at h2 h3
  nlinarith [h1, h2, h3, hdist, hray, hf]

end CatalanCore.Cert.SigmaThirds
