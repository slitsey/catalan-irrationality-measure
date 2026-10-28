module
public import CatalanCore.Uniform.Decay.Nodes.Abel
public import CatalanCore.Uniform.Decay.Nodes.Pieces
public import CatalanLambda.Decay.ThmNEnergy
@[expose] public section

/-!
# The logarithmic kernel against block pieces

* `piece_ibp`: for a piece `w, [lo, hi] ⊆ [0, b]`, `w ∫_{lo}^{hi} g` is the Stieltjes integral
  `g b · Λ_P b - ∫ g' Λ_P`.
* `kern z t = -(1/2) log ((Re z - t)² + (Im z)²) = elog z t` with explicit derivative, and the
  exact total-variation bound `∫_0^b |kern'| ≤ 2 (log M - log δ)` whenever the distance from `z`
  to `[0,b]` lies in `[δ, M]`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset MeasureTheory Set intervalIntegral

/-- The cumulative function of a piece, in the unscaled coordinate. -/
noncomputable def pieceLam (w lo hi t : ℝ) : ℝ := w * max 0 (min t hi - lo)

theorem continuous_pieceLam (w lo hi : ℝ) : Continuous (pieceLam w lo hi) := by
  unfold pieceLam
  exact continuous_const.mul (continuous_const.max ((continuous_id.min continuous_const).sub
    continuous_const))

theorem piece_ibp {g g' : ℝ → ℝ} {w lo hi b : ℝ} (h0 : 0 ≤ lo) (hlh : lo ≤ hi) (hhb : hi ≤ b)
    (hg : ∀ t ∈ Icc 0 b, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc 0 b)) :
    w * ∫ t in lo..hi, g t =
      g b * (w * (hi - lo)) - ∫ t in Ioc 0 b, g' t * pieceLam w lo hi t := by
  have hb0 : 0 ≤ b := h0.trans (hlh.trans hhb)
  rw [← intervalIntegral.integral_of_le hb0]
  have hcont : Continuous (pieceLam w lo hi) := continuous_pieceLam w lo hi
  have hF : ContinuousOn (fun t => g' t * pieceLam w lo hi t) (Icc 0 b) :=
    hg'.mul hcont.continuousOn
  have hI : ∀ x y, x ∈ Icc 0 b → y ∈ Icc 0 b →
      IntervalIntegrable (fun t => g' t * pieceLam w lo hi t) volume x y := by
    intro x y hx hy
    refine (hF.mono ?_).intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, h.1, h.2]
  have hlo : lo ∈ Icc 0 b := ⟨h0, hlh.trans hhb⟩
  have hhi : hi ∈ Icc 0 b := ⟨h0.trans hlh, hhb⟩
  have h00 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb0⟩
  have hbb : b ∈ Icc 0 b := ⟨hb0, le_rfl⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 lo h00 hlo) (hI lo b hlo hbb),
    ← intervalIntegral.integral_add_adjacent_intervals (hI lo hi hlo hhi) (hI hi b hhi hbb)]
  -- piece on [0, lo]
  have e1 : ∫ t in (0 : ℝ)..lo, g' t * pieceLam w lo hi t = 0 := by
    have : ∀ t ∈ uIcc (0 : ℝ) lo, g' t * pieceLam w lo hi t = 0 := by
      intro t ht
      rw [Set.uIcc_of_le h0] at ht
      unfold pieceLam
      have : min t hi - lo ≤ 0 := by linarith [ht.2, min_le_left t hi]
      rw [max_eq_left this]; simp
    rw [intervalIntegral.integral_congr this]; simp
  -- piece on [hi, b]
  have e3 : ∫ t in hi..b, g' t * pieceLam w lo hi t = w * (hi - lo) * (g b - g hi) := by
    have : ∀ t ∈ uIcc hi b, g' t * pieceLam w lo hi t = (w * (hi - lo)) * g' t := by
      intro t ht
      rw [Set.uIcc_of_le hhb] at ht
      unfold pieceLam
      rw [min_eq_right ht.1, max_eq_right (by linarith)]; ring
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (f' := g')
        (fun t ht => hg t ⟨by rw [Set.uIcc_of_le hhb] at ht; linarith [ht.1, hhi.1],
          by rw [Set.uIcc_of_le hhb] at ht; linarith [ht.2]⟩)
        ((hg'.mono (fun t ht => by
          rw [Set.uIcc_of_le hhb] at ht; exact ⟨by linarith [ht.1, hhi.1], ht.2⟩)).intervalIntegrable)]
  -- middle piece: integration by parts
  have e2 : ∫ t in lo..hi, g' t * pieceLam w lo hi t =
      w * ((hi - lo) * g hi - g lo * 0 - ∫ t in lo..hi, g t) := by
    have hm : ∀ t ∈ uIcc lo hi, g' t * pieceLam w lo hi t = w * ((t - lo) * g' t) := by
      intro t ht
      rw [Set.uIcc_of_le hlh] at ht
      unfold pieceLam
      rw [min_eq_left ht.2, max_eq_right (by linarith [ht.1])]; ring
    rw [intervalIntegral.integral_congr hm, intervalIntegral.integral_const_mul]
    have hsub : ∀ t ∈ uIcc lo hi, t ∈ Icc 0 b := by
      intro t ht
      rw [Set.uIcc_of_le hlh] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := lo) (b := hi)
      (u := fun t => t - lo) (u' := fun _ => (1 : ℝ)) (v := g) (v' := g')
      (fun x _ => (hasDerivAt_id x).sub_const lo) (fun x hx => hg x (hsub x hx))
      (by simp) ((hg'.mono (fun t ht => hsub t ht)).intervalIntegrable)
    simp only [one_mul, sub_self, zero_mul, mul_zero, sub_zero] at this ⊢
    rw [this]
  rw [e1, e2, e3]
  ring

/-- The distance-kernel `-(1/2) log ((Re z - t)² + (Im z)²)` (equal to `elog z t`). -/
noncomputable def kern (z : ℂ) (t : ℝ) : ℝ := -(1 / 2) * Real.log ((z.re - t) ^ 2 + z.im ^ 2)

noncomputable def kern' (z : ℂ) (t : ℝ) : ℝ := (z.re - t) / ((z.re - t) ^ 2 + z.im ^ 2)

theorem kern_eq_elog (z : ℂ) (t : ℝ) : kern z t = CatalanLambda.Decay.elog z (t : ℂ) := by
  unfold kern CatalanLambda.Decay.elog
  have h : ‖z - (t : ℂ)‖ ^ 2 = (z.re - t) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  rw [← h, Real.log_pow]
  push_cast
  ring

theorem hasDerivAt_kern (z : ℂ) (t : ℝ) (h : (z.re - t) ^ 2 + z.im ^ 2 ≠ 0) :
    HasDerivAt (kern z) (kern' z t) t := by
  have h1 : HasDerivAt (fun t : ℝ => (z.re - t) ^ 2 + z.im ^ 2) (2 * (z.re - t) * (-1)) t := by
    have := (((hasDerivAt_id t).const_sub z.re).pow 2).add_const (z.im ^ 2)
    simpa using this
  have h2 := (h1.log h).const_mul (-(1 / 2))
  refine h2.congr_deriv ?_
  unfold kern'
  field_simp

theorem continuous_kern' (z : ℂ) (b : ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ t ∈ Icc (0 : ℝ) b, δ ≤ ‖z - (t : ℂ)‖) : ContinuousOn (kern' z) (Icc 0 b) := by
  unfold kern'
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ?_)
  have h := hd t ht
  have h2 : ‖z - (t : ℂ)‖ ^ 2 = (z.re - t) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [← h2]
  exact (pow_pos (hδ.trans_le h) 2).ne'

end CatalanCore.Uniform.Decay.Nodes
