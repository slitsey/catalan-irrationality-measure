module

public import CatalanCore.Cert.SigmaHybS.Symm

@[expose] public section

/-!
# The tail bound: `g_h ≥ m′` on the slope-`5/2` ray for `u ≥ 3/2`, `|δ| ≤ 2^-30`, and `‖c k‖ ≤ 2`

All atoms lie in `[-8/25, 1] × [-43/100, 43/100]`.  Then `|z - c|² + ρ² ≤ 11 u²` for `z = -7/50 + δ - u + (5/2) u i`,
so `U^σ_m(z) ≥ -(9/16) log (11 u²)`, `U^τ(z) ≤ -log((5/2)u)`, `U^ex(z) ≤ -(1/8) log((5/2)u)` (distance to `[0,1+1/4]`
at least `Im z`), and the field term is `(999/1000) π (5/2) u ≥ 11`.
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000

def posOK (k : ℕ) : Bool :=
  decide (-(8 * 2 ^ 40 : ℤ) ≤ 25 * (ptAt k).1) && decide ((ptAt k).1 ≤ 2 ^ 40) &&
    decide (100 * (ptAt k).2.1 ≤ 43 * 2 ^ 40) && decide (-(43 * 2 ^ 40 : ℤ) ≤ 100 * (ptAt k).2.1)

theorem pos_check : (List.range 1650).all posOK = true := by decide +kernel

lemma pos_bounds (k : Fin 1650) :
    -(8 / 25 : ℝ) ≤ (cH k).re ∧ (cH k).re ≤ 1 ∧ -(43 / 100 : ℝ) ≤ (cH k).im ∧ (cH k).im ≤ 43 / 100 := by
  have h := List.all_eq_true.mp pos_check k (List.mem_range.mpr k.2)
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have r1 : (-(8 * 2 ^ 40 : ℝ)) ≤ 25 * ((ptAt k).1 : ℝ) := by exact_mod_cast h1
  have r2 : ((ptAt k).1 : ℝ) ≤ 2 ^ 40 := by exact_mod_cast h2
  have r3 : 100 * ((ptAt k).2.1 : ℝ) ≤ 43 * 2 ^ 40 := by exact_mod_cast h3
  have r4 : (-(43 * 2 ^ 40 : ℝ)) ≤ 100 * ((ptAt k).2.1 : ℝ) := by exact_mod_cast h4
  simp only [cH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem cH_norm (k : Fin 1650) : ‖cH k‖ ≤ 2 := by
  obtain ⟨a, b, c, d⟩ := pos_bounds k
  have h := Complex.norm_le_abs_re_add_abs_im (cH k)
  have h1 : |(cH k).re| ≤ 1 := abs_le.2 ⟨by linarith, b⟩
  have h2 : |(cH k).im| ≤ 43 / 100 := abs_le.2 ⟨by linarith, d⟩
  linarith

theorem tail_pt (c : ℂ) (h1 : -(8 / 25 : ℝ) ≤ c.re) (h2 : c.re ≤ 1) (h3 : -(43 / 100 : ℝ) ≤ c.im)
    (h4 : c.im ≤ 43 / 100) (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    ‖(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) - c‖ ^ 2 + (1 / 4096 : ℝ) ^ 2 ≤ 11 * u ^ 2 := by
  have hδ0 : |δ| ≤ 1 / 100 := hδ.trans (by norm_num)
  have hδ' := abs_le.mp hδ0
  have e : ‖(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) - c‖ ^ 2
      = (-(7 / 50 : ℝ) + δ - u - c.re) ^ 2 + (5 / 2 * u - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [e]
  have ha : (-(7 / 50 : ℝ) + δ - u - c.re) ^ 2 ≤ (u + 23 / 20) ^ 2 :=
    sq_le_sq' (by linarith [hδ'.1, hδ'.2]) (by linarith [hδ'.1, hδ'.2])
  have hb : (5 / 2 * u - c.im) ^ 2 ≤ (5 / 2 * u + 43 / 100) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu)]

theorem Usig_tail_lb (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    -(9 / 16) * Real.log (11 * u ^ 2) ≤
      CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ := by
  have hu0 : 0 < u := by linarith
  unfold CatalanLambda.Decay.Usig
  have h1 : ∀ k : Fin 1650, mH k * (-(1 / 2) * Real.log (11 * u ^ 2)) ≤
      mH k * CatalanLambda.Decay.krho (1 / 4096 : ℝ) ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ (cH k) := by
    intro k
    have hm : 0 ≤ mH k := by unfold mH; positivity
    apply mul_le_mul_of_nonneg_left _ hm
    unfold CatalanLambda.Decay.krho
    obtain ⟨b1, b2, b3, b4⟩ := pos_bounds k
    have hp : 0 < ‖(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ) - cH k‖ ^ 2 + (1 / 4096 : ℝ) ^ 2 := by positivity
    have := Real.log_le_log hp (tail_pt (cH k) b1 b2 b3 b4 u δ hu hδ)
    linarith
  calc -(9 / 16) * Real.log (11 * u ^ 2) = ∑ k, mH k * (-(1 / 2) * Real.log (11 * u ^ 2)) := by
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
    (217129 / 100000 : ℝ) ≤ gHyb ⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ := by
  have hu0 : 0 < u := by linarith
  have h1 := Usig_tail_lb u δ hu hδ
  have h2 := Utau_tail_ub u δ hu
  have h3 := Uex_tail_ub u δ hu
  have l11 : Real.log (11 * u ^ 2) = Real.log 11 + 2 * Real.log u := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have l25 : Real.log (5 / 2 * u) = Real.log (5 / 2) + Real.log u := Real.log_mul (by norm_num) hu0.ne'
  have h11 : Real.log 11 ≤ 10 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 by norm_num); linarith
  have h25 : 0 ≤ Real.log (5 / 2) := Real.log_nonneg (by norm_num)
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  rw [gHyb_eq]
  have him : |(⟨-(7 / 50 : ℝ) + δ - u, 5 / 2 * u⟩ : ℂ).im| = 5 / 2 * u :=
    abs_of_pos (by show 0 < 5 / 2 * u; positivity)
  rw [him]
  unfold CatalanCore.Decay.Unu
  have hf : (1 - (1 / 1000 : ℝ)) * Real.pi * (5 / 2 * u) ≥ 11 := by nlinarith
  rw [l11] at h1
  rw [l25] at h2 h3
  nlinarith [h1, h2, h3, h11, h25, hf]

end CatalanCore.Cert.SigmaHybS
