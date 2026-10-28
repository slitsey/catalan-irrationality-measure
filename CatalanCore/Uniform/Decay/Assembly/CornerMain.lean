module

public import CatalanCore.Uniform.Decay.Assembly.Corner

@[expose] public section

/-!
# Singular-corner boundary energy, part 3: the limit `ε → 0⁺`

**`boundary_energy_corner`** (`PD A B C m K`, `b, d > 0`): the identity of
`boundary_energy_identity` with `a = c = 0`,
`(i+j+2) ∫₀ᵇ∫₀ᵈ s^i t^j L = ∫₀ᵈ (bⁱ⁺¹ t^j L(b,t) - 0) dt + ∫₀ᵇ (s^i dʲ⁺¹ L(s,d) - 0) ds
   - bⁱ⁺¹ dʲ⁺¹ / ((i+1)(j+1))`
(written with the literal `0` terms so that it is a drop-in for the smooth statement).
-/

namespace CatalanCore.Uniform.Decay.Assembly

open Set intervalIntegral MeasureTheory Filter Topology
open CatalanCore.Uniform.Decay.Tools

variable {A B C m K : ℝ}

theorem tendsto_G (h : PD A B C m K) (i j : ℕ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Tendsto (fun ε : ℝ => ∫ s in ε..b, ∫ t in ε..d, s ^ i * t ^ j * Lq A B C s t) (𝓝[>] 0)
      (𝓝 (∫ s in (0 : ℝ)..b, ∫ t in (0 : ℝ)..d, s ^ i * t ^ j * Lq A B C s t)) := by
  set P0 : ℝ → ℝ := fun s => Psi A B C i j d 0 s with hP0
  have hP0i : IntervalIntegrable P0 volume 0 b := h.intervalIntegrable_Psi i j hb hd le_rfl hd.le
  have hmain := tendsto_lower hb hP0i
  set c0 : ℝ := b ^ i * d ^ j with hc0
  set ω : ℝ → ℝ := fun ε => c0 * (cc m K b d * ε + (ε - ε * Real.log ε)) * b with hω
  have hωc : Continuous ω := by
    have hc := Real.continuous_mul_log
    simp only [hω]
    exact (continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_id.sub hc))).mul continuous_const
  have hω0 : Tendsto ω (𝓝[>] 0) (𝓝 0) := by
    have h0 : ω 0 = 0 := by simp [hω]
    have := hωc.continuousAt (x := 0)
    rw [ContinuousAt, h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have herr : Tendsto (fun ε : ℝ => (∫ s in ε..b, ∫ t in ε..d, s ^ i * t ^ j * Lq A B C s t)
      - ∫ s in ε..b, P0 s) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hω0
    filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hb hd) one_pos)] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    have hεb : ε < b := lt_of_lt_of_le hε1 ((min_le_left _ _).trans (min_le_left _ _))
    have hεd : ε < d := lt_of_lt_of_le hε1 ((min_le_left _ _).trans (min_le_right _ _))
    have hε1' : ε < 1 := lt_of_lt_of_le hε1 (min_le_right _ _)
    have hsub : uIcc ε b ⊆ uIcc 0 b := by
      rw [uIcc_of_le hεb.le, uIcc_of_le hb.le]; exact Icc_subset_Icc hε0.le le_rfl
    have i1 : IntervalIntegrable (fun s => Psi A B C i j d ε s) volume ε b :=
      (h.intervalIntegrable_Psi i j hb hd hε0.le hεd.le).mono_set hsub
    have i2 : IntervalIntegrable P0 volume ε b := hP0i.mono_set hsub
    have e1 : (∫ s in ε..b, ∫ t in ε..d, s ^ i * t ^ j * Lq A B C s t) - ∫ s in ε..b, P0 s
        = ∫ s in ε..b, (Psi A B C i j d ε s - P0 s) := by
      rw [intervalIntegral.integral_sub i1 i2]; rfl
    rw [e1]
    -- pointwise bound for s ∈ (ε, b]
    have hω0' : 0 ≤ c0 * (cc m K b d * ε + (ε - ε * Real.log ε)) := by
      have hl : Real.log ε ≤ 0 := Real.log_nonpos hε0.le hε1'.le
      have hel : ε * Real.log ε ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε0.le hl
      have hc0' : 0 ≤ c0 := by rw [hc0]; positivity
      exact mul_nonneg hc0' (by nlinarith [mul_nonneg (cc_nonneg m K b d) hε0.le])
    have hpt : ∀ s ∈ Set.uIoc ε b,
        ‖Psi A B C i j d ε s - P0 s‖ ≤ c0 * (cc m K b d * ε + (ε - ε * Real.log ε)) := by
      intro s hs
      rw [Set.uIoc_of_le hεb.le] at hs
      have hs0 : 0 < s := lt_trans hε0 hs.1
      have hint1 : IntervalIntegrable (fun t => ff A B C i j s t) volume 0 d :=
        h.intervalIntegrable_ff i j hs0.ne' 0 d
      have hint2 : IntervalIntegrable (fun t => ff A B C i j s t) volume 0 ε :=
        h.intervalIntegrable_ff i j hs0.ne' 0 ε
      have e2 : Psi A B C i j d ε s - P0 s = -(∫ t in (0 : ℝ)..ε, ff A B C i j s t) := by
        have := intervalIntegral.integral_interval_sub_left hint1 hint2
        simp only [hP0, Psi]
        linarith
      rw [e2, norm_neg]
      have hbd : IntervalIntegrable (fun t : ℝ => c0 * (cc m K b d + |Real.log t|)) volume 0 ε := by
        have h1 : IntervalIntegrable (fun t : ℝ => |Real.log t|) volume 0 ε :=
          (intervalIntegral.intervalIntegrable_log').abs
        exact (intervalIntegrable_const.add h1).const_mul _
      have h3 := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := ε) hε0.le
        (f := fun t => ff A B C i j s t)
        (g := fun t : ℝ => c0 * (cc m K b d + |Real.log t|))
        (Filter.Eventually.of_forall (fun t ht => by
          rw [Real.norm_eq_abs]
          exact ff_bound h i j hs0 hs.2 ht.1 (ht.2.trans hεd.le))) hbd
      refine h3.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        intervalIntegrable_const (intervalIntegral.intervalIntegrable_log').abs,
        intervalIntegral.integral_const]
      have := Tools.integral_abs_log_zero ε hε0.le hε1'.le
      simp only [smul_eq_mul, sub_zero]
      rw [this]
      ring
    have h4 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have h5 : |b - ε| ≤ b := by rw [abs_of_pos (by linarith)]; linarith
    refine h4.trans ?_
    rw [hω]
    exact mul_le_mul_of_nonneg_left h5 hω0'
  have := hmain.add herr
  simp only [add_zero] at this
  refine this.congr (fun ε => ?_)
  ring

end CatalanCore.Uniform.Decay.Assembly
