module

public import CatalanCore.Cert.SigmaHyb.HSymm
public import CatalanLambda.Cert.Tail

@[expose] public section

/-!
# The tail bound for the hybrid: `g_h ≥ m′` on the ray for `u ≥ 3/2`

`U_ρ^σ(z) ≥ -½ log(12u²)`, `U^τ(z) ≤ -log(3u)`, `U^ex_{1/4}(z) ≤ -(1/8) log(3u)` (all atoms in
`[-13/50,0] × [-7/20,7/20]`), field `(999/1000) π 3u`; total mass `9/8`.
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def posOKL (k : ℕ) : Bool :=
  decide (-(7 * 2 ^ 40 : ℤ) ≤ 25 * (ptAtL lamS k).1) && decide ((ptAtL lamS k).1 ≤ 0) &&
    decide (5 * (ptAtL lamS k).2.1 ≤ 2 * 2 ^ 40) && decide (-(2 * 2 ^ 40 : ℤ) ≤ 5 * (ptAtL lamS k).2.1)

theorem posL_check : (List.range 180).all posOKL = true := by decide +kernel

lemma posL_bounds (k : Fin 180) :
    -(7 / 25 : ℝ) ≤ (cL k).re ∧ (cL k).re ≤ 0 ∧ -(2 / 5 : ℝ) ≤ (cL k).im ∧ (cL k).im ≤ 2 / 5 := by
  have h := List.all_eq_true.mp posL_check k (List.mem_range.mpr k.2)
  simp only [posOKL, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have r1 : (-(7 * 2 ^ 40 : ℝ)) ≤ 25 * ((ptAtL lamS k).1 : ℝ) := by exact_mod_cast h1
  have r2 : ((ptAtL lamS k).1 : ℝ) ≤ 0 := by exact_mod_cast h2
  have r3 : 5 * ((ptAtL lamS k).2.1 : ℝ) ≤ 2 * 2 ^ 40 := by exact_mod_cast h3
  have r4 : (-(2 * 2 ^ 40 : ℝ)) ≤ 5 * ((ptAtL lamS k).2.1 : ℝ) := by exact_mod_cast h4
  simp only [cL, cOfL]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg r2 (by positivity)
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

lemma pos_all (k : Fin (300 + 180)) :
    -(7 / 25 : ℝ) ≤ (cH k).re ∧ (cH k).re ≤ 0 ∧ -(2 / 5 : ℝ) ≤ (cH k).im ∧ (cH k).im ≤ 2 / 5 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [cH, Fin.append_left]
    obtain ⟨a, b, c, d⟩ := pos_bounds i
    exact ⟨by linarith, b, by linarith, by linarith⟩
  · simp only [cH, Fin.append_right]; exact posL_bounds i

theorem tail_pt (c : ℂ) (h1 : -(7 / 25 : ℝ) ≤ c.re) (h2 : c.re ≤ 0) (h3 : -(2 / 5 : ℝ) ≤ c.im)
    (h4 : c.im ≤ 2 / 5) (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    ‖(⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ : ℂ) - c‖ ^ 2 + (1 / 1024 : ℝ) ^ 2 ≤ 12 * u ^ 2 := by
  have hδ' := abs_le.mp hδ
  have hW : (1 / 2 ^ 30 : ℝ) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; norm_num
  have e : ‖(⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ : ℂ) - c‖ ^ 2
      = (-(7 / 50 : ℝ) + δ - u - c.re) ^ 2 + (3 * u - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [e]
  have ha : (-(7 / 50 : ℝ) + δ - u - c.re) ^ 2 ≤ (u + 3 / 20) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have hb : (3 * u - c.im) ^ 2 ≤ (3 * u + 2 / 5) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hu) (by linarith : (0 : ℝ) ≤ u)]

theorem Usig_tail_lb (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    -(1 / 2) * Real.log (12 * u ^ 2) ≤
      CatalanLambda.Decay.Usig (1 / 1024 : ℝ) cH wtH ⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ := by
  have hu0 : 0 < u := by linarith
  unfold CatalanLambda.Decay.Usig
  have h1 : ∀ k : Fin (300 + 180), wtH k * (-(1 / 2) * Real.log (12 * u ^ 2)) ≤
      wtH k * CatalanLambda.Decay.krho (1 / 1024 : ℝ) ⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ (cH k) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (wtH_nonneg k)
    unfold CatalanLambda.Decay.krho
    obtain ⟨b1, b2, b3, b4⟩ := pos_all k
    have hp : 0 < ‖(⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ : ℂ) - cH k‖ ^ 2 + (1 / 1024 : ℝ) ^ 2 := by positivity
    have := Real.log_le_log hp (tail_pt (cH k) b1 b2 b3 b4 u δ hu hδ)
    linarith
  calc -(1 / 2) * Real.log (12 * u ^ 2) = ∑ k, wtH k * (-(1 / 2) * Real.log (12 * u ^ 2)) := by
        rw [← Finset.sum_mul, wtH_sum, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun k _ => h1 k)

theorem Utau_tail_ub (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) :
    CatalanLambda.Decay.Utau (⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ : ℂ) ≤ -Real.log (3 * u) := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ with hz
  unfold CatalanLambda.Decay.Utau
  have hge : ∀ t : ℝ, 3 * u ≤ ‖z - (t : ℂ)‖ := by
    intro t
    have h := Complex.abs_im_le_norm (z - (t : ℂ))
    have e : (z - (t : ℂ)).im = 3 * u := by simp [hz]
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
    hcont.intervalIntegrable (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -Real.log (3 * u)) MeasureTheory.volume 0 1)
    (fun t _ => by
      have := Real.log_le_log (by positivity) (hge t)
      linarith)
  simpa using hmono

theorem Uex_tail_ub (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) :
    CatalanCore.Decay.Uex (2 * (1 / 8 : ℝ)) (⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ : ℂ)
      ≤ -(1 / 8) * Real.log (3 * u) := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ with hz
  unfold CatalanCore.Decay.Uex
  have hge : ∀ t : ℝ, 3 * u ≤ ‖z - (t : ℂ)‖ := by
    intro t
    have h := Complex.abs_im_le_norm (z - (t : ℂ))
    have e : (z - (t : ℂ)).im = 3 * u := by simp [hz]
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
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -Real.log (3 * u)) MeasureTheory.volume 1 (1 + 2 * (1 / 8)))
    (fun t _ => by
      unfold CatalanLambda.Decay.elog
      have := Real.log_le_log (by positivity) (hge t)
      linarith)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have e : (1 + 2 * (1 / 8 : ℝ) - 1) = 1 / 4 := by norm_num
  rw [e] at hmono
  linarith

theorem tail_hyb (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    (22147 / 10000 : ℝ) ≤ gHyb ⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ := by
  have hu0 : 0 < u := by linarith
  have h1 := Usig_tail_lb u δ hu hδ
  have h2 := Utau_tail_ub u δ hu
  have h3 := Uex_tail_ub u δ hu
  have hlog : -(1 / 6 : ℝ) ≤ Real.log (3 * u) - (1 / 2) * Real.log (12 * u ^ 2) := by
    have h9 : Real.log ((3 * u) ^ 2) = 2 * Real.log (3 * u) := by rw [Real.log_pow]; push_cast; ring
    have h := Real.log_le_sub_one_of_pos (show 0 < 12 * u ^ 2 / (3 * u) ^ 2 by positivity)
    rw [Real.log_div (by positivity) (by positivity), h9] at h
    have e : 12 * u ^ 2 / (3 * u) ^ 2 - 1 = (1 / 3 : ℝ) := by field_simp; ring
    rw [e] at h
    linarith
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  unfold gHyb CatalanCore.Cert.gAlpha CatalanCore.Decay.Unu
  have him : |(⟨-(7 / 50 : ℝ) + δ - u, 3 * u⟩ : ℂ).im| = 3 * u := abs_of_pos (by show 0 < 3 * u; positivity)
  rw [him]
  have hf : (1 - 1 / 1000 : ℝ) * Real.pi * (3 * u) ≥ 14 := by nlinarith
  push_cast
  nlinarith [h1, h2, h3, hlog, hf]

end CatalanCore.Cert.SigmaHyb
