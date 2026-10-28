module
public import CatalanCore.Uniform.Decay.Nodes.Kernel
@[expose] public section

/-!
# Total variation of the logarithmic kernel

For `z : ℂ` whose distance to every `t ∈ [0, b]` lies in `[δ, M]`, the kernel `kern z`
(`= elog z t`) is increasing then decreasing, with
`∫_0^b |kern' z| ≤ 2 (log M - log δ)` and `kern z t ∈ [-log M, -log δ]`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset MeasureTheory Set intervalIntegral

section
variable {z : ℂ} {b δ M : ℝ}

theorem kern_le (hb : 0 ≤ b) (hδ : 0 < δ) (hd : ∀ t ∈ Icc (0 : ℝ) b, δ ≤ ‖z - (t : ℂ)‖)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) : kern z t ≤ -Real.log δ := by
  rw [kern_eq_elog]
  unfold CatalanLambda.Decay.elog
  have := Real.log_le_log hδ (hd t ht)
  linarith

theorem ge_kern (hb : 0 ≤ b) (hδ : 0 < δ) (hd : ∀ t ∈ Icc (0 : ℝ) b, δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) b, ‖z - (t : ℂ)‖ ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) :
    -Real.log M ≤ kern z t := by
  rw [kern_eq_elog]
  unfold CatalanLambda.Decay.elog
  have := Real.log_le_log (hδ.trans_le (hd t ht)) (hM t ht)
  linarith

theorem integral_kern' (hb : 0 ≤ b) (hδ : 0 < δ) (hd : ∀ t ∈ Icc (0 : ℝ) b, δ ≤ ‖z - (t : ℂ)‖)
    {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ b) :
    ∫ t in a..c, kern' z t = kern z c - kern z a := by
  have hnz : ∀ t ∈ Icc (0 : ℝ) b, (z.re - t) ^ 2 + z.im ^ 2 ≠ 0 := by
    intro t ht
    have h2 : ‖z - (t : ℂ)‖ ^ 2 = (z.re - t) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [← h2]
    exact (pow_pos (hδ.trans_le (hd t ht)) 2).ne'
  have hsub : uIcc a c ⊆ Icc 0 b := by
    rw [Set.uIcc_of_le hac]
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_kern z t (hnz t (hsub ht)))
    (((continuous_kern' z b δ hδ hd).mono hsub).intervalIntegrable)

/-- **Total variation** of the logarithmic kernel along `[0, b]`. -/
theorem kern_variation (hb : 0 ≤ b) (hδ : 0 < δ)
    (hd : ∀ t ∈ Icc (0 : ℝ) b, δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) b, ‖z - (t : ℂ)‖ ≤ M) :
    ∫ t in Ioc 0 b, |kern' z t| ≤ 2 * (Real.log M - Real.log δ) := by
  rw [← intervalIntegral.integral_of_le hb]
  have hcont : ContinuousOn (kern' z) (Icc 0 b) := continuous_kern' z b δ hδ hd
  have hI : ∀ x y, x ∈ Icc 0 b → y ∈ Icc 0 b →
      IntervalIntegrable (fun t => |kern' z t|) volume x y := by
    intro x y hx hy
    refine (hcont.abs.mono ?_).intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> constructor <;>
      linarith [hx.1, hx.2, hy.1, hy.2, h.1, h.2]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb⟩
  have hbb : b ∈ Icc (0 : ℝ) b := ⟨hb, le_rfl⟩
  have k0 := kern_le hb hδ hd h0
  have kb := kern_le hb hδ hd hbb
  have m0 := ge_kern hb hδ hd hM h0
  have mb := ge_kern hb hδ hd hM hbb
  have hMδ : 0 ≤ Real.log M - Real.log δ := by linarith
  have num : ∀ t, kern' z t = (z.re - t) / ((z.re - t) ^ 2 + z.im ^ 2) := fun t => rfl
  have den : ∀ t, 0 ≤ (z.re - t) ^ 2 + z.im ^ 2 := fun t => by positivity
  by_cases hneg : z.re ≤ 0
  · -- decreasing kernel derivative nonpositive
    have : ∀ t ∈ uIcc (0 : ℝ) b, |kern' z t| = -kern' z t := by
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      rw [abs_of_nonpos]
      rw [num]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) (den t)
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_neg,
      integral_kern' hb hδ hd le_rfl hb le_rfl]
    linarith
  · push Not at hneg
    by_cases hbig : b ≤ z.re
    · have : ∀ t ∈ uIcc (0 : ℝ) b, |kern' z t| = kern' z t := by
        intro t ht
        rw [Set.uIcc_of_le hb] at ht
        rw [abs_of_nonneg]
        rw [num]
        exact div_nonneg (by linarith [ht.2]) (den t)
      rw [intervalIntegral.integral_congr this, integral_kern' hb hδ hd le_rfl hb le_rfl]
      linarith
    · push Not at hbig
      have hs : z.re ∈ Icc (0 : ℝ) b := ⟨hneg.le, hbig.le⟩
      have e1 : ∀ t ∈ uIcc (0 : ℝ) z.re, |kern' z t| = kern' z t := by
        intro t ht
        rw [Set.uIcc_of_le hneg.le] at ht
        rw [abs_of_nonneg]
        rw [num]
        exact div_nonneg (by linarith [ht.2]) (den t)
      have e2 : ∀ t ∈ uIcc z.re b, |kern' z t| = -kern' z t := by
        intro t ht
        rw [Set.uIcc_of_le hbig.le] at ht
        rw [abs_of_nonpos]
        rw [num]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) (den t)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 z.re h0 hs) (hI z.re b hs hbb),
        intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
        intervalIntegral.integral_neg, integral_kern' hb hδ hd le_rfl hneg.le hbig.le,
        integral_kern' hb hδ hd hneg.le hbig.le le_rfl]
      have ks := kern_le hb hδ hd hs
      linarith

end
end CatalanCore.Uniform.Decay.Nodes
