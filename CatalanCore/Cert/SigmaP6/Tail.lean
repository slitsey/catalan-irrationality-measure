module

public import CatalanCore.Cert.SigmaP6.Symm

@[expose] public section

/-!
# The tail bound: `g ≥ m′` on the ray for `u ≥ 3/2`, `|δ| ≤ 2^-30`

Elementary: `U_ρ^σ(z) ≥ -½ log(12 u²)`, `U^τ(z) ≤ -log(3u)` (since `dist(z,[0,1]) ≥ Im z = 3u`),
the field term is `(999/1000) π 3u`.
-/

open Real

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

set_option maxRecDepth 100000

def posOK (k : ℕ) : Bool :=
  decide (-(11 * 2 ^ 40 : ℤ) ≤ 10 * (ptAt k).1) && decide ((ptAt k).1 ≤ 0) &&
    decide (10 * (ptAt k).2.1 ≤ 28 * 2 ^ 40) && decide (-(28 * 2 ^ 40 : ℤ) ≤ 10 * (ptAt k).2.1)

theorem pos_check : (List.range 699).all posOK = true := by decide +kernel

lemma pos_bounds (k : Fin 699) :
    -(11 / 10 : ℝ) ≤ (cS k).re ∧ (cS k).re ≤ 0 ∧ -(14 / 5 : ℝ) ≤ (cS k).im ∧ (cS k).im ≤ 14 / 5 := by
  have h := List.all_eq_true.mp pos_check k (List.mem_range.mpr k.2)
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have r1 : (-(11 * 2 ^ 40 : ℝ)) ≤ 10 * ((ptAt k).1 : ℝ) := by exact_mod_cast h1
  have r2 : ((ptAt k).1 : ℝ) ≤ 0 := by exact_mod_cast h2
  have r3 : 10 * ((ptAt k).2.1 : ℝ) ≤ 28 * 2 ^ 40 := by exact_mod_cast h3
  have r4 : (-(28 * 2 ^ 40 : ℝ)) ≤ 10 * ((ptAt k).2.1 : ℝ) := by exact_mod_cast h4
  simp only [cS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg r2 (by positivity)
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem tail_core (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    (1883395 / 1000000 : ℝ) ≤
      CatalanLambda.Decay.gfun (1 / 2048 : ℝ) (1 / 1000 : ℝ) cS mS ⟨-(1 / 10 : ℝ) + δ - u, 3 * u⟩ := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-(1 / 10 : ℝ) + δ - u, 3 * u⟩ with hz
  have hδ' := abs_le.mp hδ
  have hW : (1 / 2 ^ 30 : ℝ) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; norm_num
  -- (a) Usig lower bound
  have hpt : ∀ k : Fin 699, ‖z - cS k‖ ^ 2 + (1 / 2048 : ℝ) ^ 2 ≤ 30 * u ^ 2 := by
    intro k
    obtain ⟨b1, b2, b3, b4⟩ := pos_bounds k
    have e : ‖z - cS k‖ ^ 2 = (z.re - (cS k).re) ^ 2 + (z.im - (cS k).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [e]
    have hre : z.re = -(1 / 10 : ℝ) + δ - u := rfl
    have him : z.im = 3 * u := rfl
    have hd : |δ| ≤ 1 / 100 := hδ.trans (by norm_num)
    have hd' := abs_le.mp hd
    have ha : (z.re - (cS k).re) ^ 2 ≤ (u + 11 / 100) ^ 2 :=
      sq_le_sq' (by rw [hre]; linarith [hd'.1, hd'.2]) (by rw [hre]; linarith [hd'.1, hd'.2])
    have hb : (z.im - (cS k).im) ^ 2 ≤ (3 * u + 14 / 5) ^ 2 :=
      sq_le_sq' (by rw [him]; linarith) (by rw [him]; linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hu) hu0.le]
  have hUs : -(1 / 2) * Real.log (30 * u ^ 2) ≤ CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cS mS z := by
    unfold CatalanLambda.Decay.Usig
    have h1 : ∀ k : Fin 699, mS k * (-(1 / 2) * Real.log (30 * u ^ 2)) ≤ mS k * CatalanLambda.Decay.krho (1 / 2048 : ℝ) z (cS k) := by
      intro k
      have hm : 0 ≤ mS k := by unfold mS; positivity
      apply mul_le_mul_of_nonneg_left _ hm
      unfold CatalanLambda.Decay.krho
      have hp : 0 < ‖z - cS k‖ ^ 2 + (1 / 2048 : ℝ) ^ 2 := by positivity
      have := Real.log_le_log hp (hpt k)
      linarith
    calc -(1 / 2) * Real.log (30 * u ^ 2) = ∑ k, mS k * (-(1 / 2) * Real.log (30 * u ^ 2)) := by
          rw [← Finset.sum_mul, mS_sum, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun k _ => h1 k)
  -- (b) Utau upper bound
  have hUt : CatalanLambda.Decay.Utau z ≤ -Real.log (3 * u) := by
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
  -- (c) assemble
  have hlog : -(7 / 6 : ℝ) ≤ Real.log (3 * u) - (1 / 2) * Real.log (30 * u ^ 2) := by
    have h9 : Real.log ((3 * u) ^ 2) = 2 * Real.log (3 * u) := by rw [Real.log_pow]; push_cast; ring
    have h := Real.log_le_sub_one_of_pos (show 0 < 30 * u ^ 2 / (3 * u) ^ 2 by positivity)
    rw [Real.log_div (by positivity) (by positivity), h9] at h
    have e : 30 * u ^ 2 / (3 * u) ^ 2 - 1 = (7 / 3 : ℝ) := by field_simp; ring
    rw [e] at h
    linarith
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  unfold CatalanLambda.Decay.gfun
  have him : |z.im| = 3 * u := abs_of_pos (by show 0 < 3 * u; positivity)
  rw [him]
  have : (1 - 1 / 1000 : ℝ) * Real.pi * (3 * u) ≥ 14 := by nlinarith
  linarith

end CatalanCore.Cert.SigmaP6
