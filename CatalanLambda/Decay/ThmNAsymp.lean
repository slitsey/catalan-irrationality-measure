import CatalanLambda.Decay.ThmNWindow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Theorem N_ρ: `E(h) = O(h log h)`, hence `o(h²)`, and the liminf form of the window corollary
-/

open Finset Filter Topology CatalanLambda.Decay

namespace CatalanLambda.Decay

lemma tendsto_log_div_nat : Tendsto (fun h : ℕ => Real.log h / h) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at this
  exact this.comp tendsto_natCast_atTop_atTop

lemma log_lin_le (A B : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B) {h : ℕ} (hh : 1 ≤ h) :
    Real.log (A * h + B) ≤ Real.log (A + B) + Real.log h := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have : A * h + B ≤ (A + B) * h := by nlinarith
  calc Real.log (A * h + B) ≤ Real.log ((A + B) * h) :=
        Real.log_le_log (by nlinarith) this
    _ = _ := Real.log_mul (by linarith) (by linarith)

/-- `E(h) ≤ K h + 5 h log h`, and `E(h) ≥ 0`, for `h ≥ 1`. -/
theorem Eerr_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) :
    ∃ C : ℝ, ∀ h : ℕ, 1 ≤ h → 0 ≤ Eerr F h ∧ Eerr F h ≤ h * C + 5 * h * Real.log h := by
  have hA := R.Aco_pos
  have hb := R.betaE_pos F.hε0
  set cE : ℝ := 2 * (R.Aco ^ ε / R.betaE ε) with hcE
  have hcE0 : 0 ≤ cE := by positivity
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  set Γ : ℝ := ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 with hΓ
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  set Cl : ℝ := max (Real.log R.Aco) 0 with hCl
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  refine ⟨4 * Γ + |Real.log ρ| + 3 + Cl
      + 2 * Real.log (8 / 3 + 1) + Real.log (2 * F.r0 + cE + 1) + 1 / 2, ?_⟩
  intro h hh
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg h1
  have e1 : Real.log (1 + 8 * (h : ℝ) / 3) ≤ Real.log (8 / 3 + 1) + Real.log h := by
    have := log_lin_le (8 / 3) 1 (by norm_num) le_rfl hh
    have e : (1 + 8 * (h : ℝ) / 3) = 8 / 3 * h + 1 := by ring
    rw [e]; exact this
  have e2 : Real.log (2 * F.r0 * h + cE + 1) ≤ Real.log (2 * F.r0 + cE + 1) + Real.log h := by
    have := log_lin_le (2 * F.r0) (cE + 1) (by positivity) (by linarith) hh
    have e : 2 * (F.r0 : ℝ) * h + cE + 1 = 2 * F.r0 * h + (cE + 1) := by ring
    rw [e]
    have e' : 2 * (F.r0 : ℝ) + (cE + 1) = 2 * F.r0 + cE + 1 := by ring
    rw [e'] at this; exact this
  have h83 : (0 : ℝ) ≤ 8 * h / 3 := by positivity
  have hl1 : 0 ≤ Real.log (1 + 8 * (h : ℝ) / 3) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2 * F.r0 * h + cE + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ 2 * F.r0 * h := by positivity
    linarith)
  have hl8 : 0 ≤ Real.log (8 / 3 + 1 : ℝ) := Real.log_nonneg (by norm_num)
  have hl9 : 0 ≤ Real.log (2 * (F.r0 : ℝ) + cE + 1) := Real.log_nonneg (by linarith)
  unfold Eerr Rerr
  rw [← hΓ, ← hCl, ← hcE]
  constructor
  · have : 0 ≤ (h : ℝ) * Real.log (2 * F.r0 * h + cE + 1) := by positivity
    have : 0 ≤ 4 * (h : ℝ) * Γ := by positivity
    have : 0 ≤ (h : ℝ) * |Real.log ρ| := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Real.log h := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Real.log (1 + 8 * h / 3) := by positivity
    have : 0 ≤ (h : ℝ) * Cl := by positivity
    nlinarith
  · have t1 : 2 * (h : ℝ) * Real.log (1 + 8 * h / 3) ≤ 2 * h * (Real.log (8 / 3 + 1) + Real.log h) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have t2 : (h : ℝ) * Real.log (2 * F.r0 * h + cE + 1)
        ≤ h * (Real.log (2 * F.r0 + cE + 1) + Real.log h) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith

theorem Eerr_div_tendsto {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) :
    Tendsto (fun h : ℕ => Eerr F h / (h : ℝ) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Eerr_bound F
  have hup : Tendsto (fun h : ℕ => C / (h : ℝ) + 5 * (Real.log h / h)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun h : ℕ => C / (h : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using h1.add (tendsto_log_div_nat.const_mul 5)
  refine squeeze_zero' ?_ ?_ hup
  · filter_upwards [eventually_ge_atTop 1] with h hh
    exact div_nonneg (hC h hh).1 (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have h1 : (0 : ℝ) < h := by exact_mod_cast hh
    rw [div_le_iff₀ (by positivity)]
    have := (hC h hh).2
    have e : (C / (h : ℝ) + 5 * (Real.log h / h)) * (h : ℝ) ^ 2
        = h * C + 5 * h * Real.log h := by field_simp
    rw [e]; exact this

/-- **Liminf form of the window corollary.**  For every `δ > 0` there is `h₀` such that for all
`h ≥ h₀` and all `|t| ≤ e^{-c_cert h}`: `|det(T_h + t I)| ≤ exp(-(D_cert - δ) h²)`. -/
theorem window_liminf {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ t : ℝ, |t| ≤ Real.exp (-(F.ccert : ℝ) * h) →
      |(Tmat h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det|
        ≤ Real.exp (-((F.Dcert : ℝ) - δ) * (h : ℝ) ^ 2) := by
  have h1 := Eerr_div_tendsto F
  have h2 : Tendsto (fun h : ℕ => Real.log 2 / (h : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 := h1.add h2
  rw [add_zero] at h3
  have hev := (tendsto_order.1 h3).2 δ hδ
  have hW : ∀ᶠ h : ℕ in atTop, 5 / (8 * (F.W : ℝ)) ≤ h :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨h₀, hh₀⟩ := eventually_atTop.1 (hev.and (hW.and (eventually_ge_atTop 1)))
  refine ⟨h₀, fun h hh t ht => ?_⟩
  obtain ⟨hs, hW', hh1⟩ := hh₀ h hh
  have hpos : 0 < h := hh1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hpos
  refine (window F hpos hW' ht).trans (Real.exp_le_exp.2 ?_)
  have : Eerr F h / (h : ℝ) ^ 2 + Real.log 2 / h < δ := hs
  have h4 : Eerr F h + h * Real.log 2 < δ * (h : ℝ) ^ 2 := by
    have := mul_lt_mul_of_pos_right this (show (0 : ℝ) < (h : ℝ) ^ 2 by positivity)
    have e : (Eerr F h / (h : ℝ) ^ 2 + Real.log 2 / h) * (h : ℝ) ^ 2
        = Eerr F h + h * Real.log 2 := by field_simp
    rw [e] at this; exact this
  nlinarith

/-- `T_h + t I = (λ + t) I + M0` as real matrices, so `det(T_h + t I) = P_h(λ + t)` (the
polynomial `P_h(X) = det(X I + M0)` evaluated at the real number `λ + t`). -/
theorem Tmat_add_eq (h : ℕ) (t : ℝ) :
    Tmat h + t • (1 : Matrix (Fin h) (Fin h) ℝ)
      = (lamS + t) • (1 : Matrix (Fin h) (Fin h) ℝ) + (CatalanLambda.M0 h).map (Rat.cast : ℚ → ℝ) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp [Tmat, Tent, CatalanLambda.M0]; ring
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [Tmat, Tent, CatalanLambda.M0, hab, hab']

/-- The window corollary for `P_h(λ + t)`. -/
theorem window_liminf_P {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ t : ℝ, |t| ≤ Real.exp (-(F.ccert : ℝ) * h) →
      |((lamS + t) • (1 : Matrix (Fin h) (Fin h) ℝ)
          + (CatalanLambda.M0 h).map (Rat.cast : ℚ → ℝ)).det|
        ≤ Real.exp (-((F.Dcert : ℝ) - δ) * (h : ℝ) ^ 2) := by
  obtain ⟨h₀, H⟩ := window_liminf F hδ
  exact ⟨h₀, fun h hh t ht => by rw [← Tmat_add_eq]; exact H h hh t ht⟩

end CatalanLambda.Decay
