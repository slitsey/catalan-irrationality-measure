module

public import CatalanCore.Uniform.Decay.Cells.Rules

@[expose] public section

/-!
# Far cells and the tail (lane D, package D6)

Mass cancellation `|M U0 - Vnu| ≤ 2 M₁ / ‖z‖` for `‖z‖ ≥ T₀` (hypothesis `FarHyp`, supplied by the
node/atom instance; D4's `abs_mul_logPot_sub_logPot_le` is the source) gives, for every `z` with
`Im z ≥ T ≥ T₀`,  `g z ≥ (1-ε) π T - 2 M₁ / T`.  The rational test `farOk` uses `π ≥ 3.141592`.
Far ray cells (`rayFarOk`) and the tail rule (`tailFarOk`, tail `u ≥ umax`) are instances of one
lemma (the shape of D4's `tail_rule`).
-/

namespace CatalanCore.Uniform.Decay.Cells

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline

/-- Far-field constants: `M₁` (mass-cancellation constant) and `T₀` (radius beyond which it holds). -/
structure FarData where
  M1 : ℚ
  T0 : ℚ

/-- The semantic hypothesis on the second potential. -/
structure FarHyp (D : SplineData) (Vnu : ℂ → ℝ) (F : FarData) : Prop where
  hM1 : 0 ≤ F.M1
  hT0 : 0 < F.T0
  hΔ : ∀ z : ℂ, (F.T0 : ℝ) ≤ ‖z‖ →
    |(D.Mq : ℝ) * U0 D.A D.B D.f z - Vnu z| ≤ 2 * (F.M1 : ℝ) / ‖z‖

/-- Rational lower bound for `π`. -/
def piLo : ℚ := 3141592 / 1000000

theorem piLo_lt : (piLo : ℝ) < Real.pi := by
  have := Real.pi_gt_d6
  unfold piLo
  norm_num at this ⊢
  linarith

/-- Rational test: `T₀ ≤ T` and `m' ≤ (1-ε) π_lo T - 2 M₁ / T`. -/
def farOk (D : SplineData) (F : FarData) (T : ℚ) : Bool :=
  decide (F.T0 ≤ T) && decide (D.mprime ≤ (1 - D.ε) * piLo * T - 2 * F.M1 / T)

/-- **Far lemma.** -/
theorem far_g_ge {D : SplineData} {Vnu : ℂ → ℝ} {F : FarData} (H : FarHyp D Vnu F)
    (B : SplineData.BasicFacts D) {T : ℚ} (h : farOk D F T = true) (z : ℂ) (hz : (T : ℝ) ≤ z.im) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f z := by
  simp only [farOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hT0, hm⟩ := h
  have hT0R : (F.T0 : ℝ) ≤ T := by exact_mod_cast hT0
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by exact_mod_cast H.hT0) hT0R
  have hmR : (D.mprime : ℝ) ≤ (1 - (D.ε : ℝ)) * (piLo : ℝ) * T - 2 * (F.M1 : ℝ) / T := by
    have := (Rat.cast_le (K := ℝ)).2 hm
    push_cast at this
    exact this
  have hzn : (T : ℝ) ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_im_le_norm z))
  have h1 := H.hΔ z (hT0R.trans hzn)
  have h2 : 2 * (F.M1 : ℝ) / ‖z‖ ≤ 2 * (F.M1 : ℝ) / T :=
    div_le_div_of_nonneg_left (by have := H.hM1; positivity) hTpos hzn
  have h3 : -(2 * (F.M1 : ℝ) / T) ≤ (D.Mq : ℝ) * U0 D.A D.B D.f z - Vnu z := by
    have := neg_abs_le ((D.Mq : ℝ) * U0 D.A D.B D.f z - Vnu z); linarith
  have hκ : 0 ≤ 1 - (D.ε : ℝ) := by linarith [B.hε1]
  have h4 : (1 - (D.ε : ℝ)) * (piLo : ℝ) * T ≤ (1 - (D.ε : ℝ)) * Real.pi * |z.im| := by
    have hpl := piLo_lt
    have : (piLo : ℝ) * T ≤ Real.pi * |z.im| := by
      have : T ≤ |z.im| := hz.trans (le_abs_self _)
      have hp0 : 0 ≤ (piLo : ℝ) := by unfold piLo; norm_num
      nlinarith
    nlinarith
  unfold gNu
  linarith

/-- Far ray cell `[p.1, p.2]`: `Im z ≥ sl p.1`. -/
def rayFarOk (D : SplineData) (F : FarData) (p : ℚ × ℚ) : Bool := farOk D F (D.sl * p.1)

theorem rayFar_sound {D : SplineData} {Vnu : ℂ → ℝ} {F : FarData} (H : FarHyp D Vnu F)
    (B : SplineData.BasicFacts D) {p : ℚ × ℚ} (h : rayFarOk D F p = true) (x y : ℝ)
    (hy : (D.sl : ℝ) * (p.1 : ℝ) ≤ y) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, y⟩ := by
  refine far_g_ge H B (T := D.sl * p.1) h ⟨x, y⟩ ?_
  push_cast
  exact hy

/-- Tail `u ≥ umax`: needs `0 < sl`, `0 < umax`. -/
def tailFarOk (D : SplineData) (F : FarData) : Bool :=
  decide (0 < D.sl) && decide (0 < D.umax) && farOk D F (D.sl * D.umax)

theorem tailFar_sound {D : SplineData} {Vnu : ℂ → ℝ} {F : FarData} (H : FarHyp D Vnu F)
    (B : SplineData.BasicFacts D) (h : tailFarOk D F = true) (u δ : ℝ) (hu : (D.umax : ℝ) ≤ u) :
    (D.mprime : ℝ) ≤
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨-(D.r0 : ℝ) + δ - u, (D.sl : ℝ) * u⟩ := by
  simp only [tailFarOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, -⟩, hf⟩ := h
  refine far_g_ge H B hf _ ?_
  have hs' : (0 : ℝ) < D.sl := by exact_mod_cast hs
  push_cast
  show (D.sl : ℝ) * D.umax ≤ (D.sl : ℝ) * u
  exact mul_le_mul_of_nonneg_left hu hs'.le

end CatalanCore.Uniform.Decay.Cells
