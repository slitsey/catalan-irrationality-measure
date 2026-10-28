module

public import CatalanCore.Uniform.Decay.Tools.BoundaryEnergy
public import CatalanCore.Uniform.Decay.Tools.LogModulusLemmas

@[expose] public section

/-!
# Singular-corner boundary energy, part 1: bounds on `L` and the vanishing edge terms

`PD A B C m K`: the quadratic form `qf A B C s t = A s² + 2 B s t + C t²` satisfies
`m (s² + t²) ≤ qf ≤ K (s² + t²)` with `m > 0` (positive definite: the two supporting lines are
distinct).  Then `L = ½ log qf` is logarithmically bounded near the singular corner `(0,0)`,
and the boundary terms of the identity on `[ε, b] × [ε, d]` at the edges `s = ε`, `t = ε`
vanish as `ε → 0⁺`.
-/

namespace CatalanCore.Uniform.Decay.Assembly

open Set intervalIntegral MeasureTheory Filter Topology
open CatalanCore.Uniform.Decay.Tools

/-- Two-sided quadratic bounds for the form (positive definite case). -/
structure PD (A B C m K : ℝ) : Prop where
  m_pos : 0 < m
  lower : ∀ s t : ℝ, m * (s ^ 2 + t ^ 2) ≤ qf A B C s t
  upper : ∀ s t : ℝ, qf A B C s t ≤ K * (s ^ 2 + t ^ 2)

theorem PD.K_pos {A B C m K : ℝ} (h : PD A B C m K) : 0 < K := by
  have h1 := h.lower 1 0
  have h2 := h.upper 1 0
  have := h.m_pos
  nlinarith

theorem Lq_comm (A B C s t : ℝ) : Lq A B C s t = Lq C B A t s := by
  unfold Lq qf; congr 2; ring

theorem PD.swap {A B C m K : ℝ} (h : PD A B C m K) : PD C B A m K where
  m_pos := h.m_pos
  lower s t := by have := h.lower t s; unfold qf at *; nlinarith
  upper s t := by have := h.upper t s; unfold qf at *; nlinarith

theorem abs_log_le_of_bounds {p x q : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    |Real.log x| ≤ |Real.log p| + |Real.log q| := by
  have hx : 0 < x := lt_of_lt_of_le hp hpx
  have h1 : Real.log p ≤ Real.log x := Real.log_le_log hp hpx
  have h2 : Real.log x ≤ Real.log q := Real.log_le_log hx hxq
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log p); have := abs_nonneg (Real.log q); linarith
  · have := le_abs_self (Real.log q); have := abs_nonneg (Real.log p); linarith

/-- Logarithmic bound for `L` on the shell `ρ ≤ s² + t² ≤ R`. -/
theorem PD.Lq_bound {A B C m K : ℝ} (h : PD A B C m K) {s t ρ R : ℝ} (hρ : 0 < ρ)
    (h1 : ρ ≤ s ^ 2 + t ^ 2) (h2 : s ^ 2 + t ^ 2 ≤ R) :
    |Lq A B C s t| ≤ (|Real.log m| + |Real.log ρ| + |Real.log K| + |Real.log R|) / 2 := by
  have hK := h.K_pos
  have hm := h.m_pos
  have hR : 0 < R := lt_of_lt_of_le hρ (h1.trans h2)
  have hlow : m * ρ ≤ qf A B C s t := (mul_le_mul_of_nonneg_left h1 hm.le).trans (h.lower s t)
  have hup : qf A B C s t ≤ K * R :=
    (h.upper s t).trans (mul_le_mul_of_nonneg_left h2 hK.le)
  have hb := abs_log_le_of_bounds (mul_pos hm hρ) hlow hup
  rw [Real.log_mul hm.ne' hρ.ne', Real.log_mul hK.ne' hR.ne'] at hb
  unfold Lq
  rw [abs_div, abs_two]
  have e1 := abs_add_le (Real.log m) (Real.log ρ)
  have e2 := abs_add_le (Real.log K) (Real.log R)
  have := abs_nonneg (Real.log m)
  linarith

/-- The edge terms vanish: `ε^(p+1) ∫_ε^d t^q L(ε,t) dt → 0`. -/
theorem edge_vanish {A B C m K : ℝ} (h : PD A B C m K) (p q : ℕ) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun ε : ℝ => ε ^ (p + 1) * ∫ t in ε..d, t ^ q * Lq A B C ε t) (𝓝[>] 0) (𝓝 0) := by
  set c1 : ℝ := (|Real.log m| + |Real.log K| + |Real.log (1 + d ^ 2)|) / 2 with hc1
  set F : ℝ → ℝ := fun ε => d ^ (q + 1) * (c1 * ε + |ε * Real.log ε|) with hF
  have hFc : Continuous F := by
    have := Real.continuous_mul_log
    simp only [hF]
    fun_prop
  have hF0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h0 : F 0 = 0 := by simp [hF]
    have := hFc.continuousAt (x := 0)
    rw [ContinuousAt, h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hF0
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (min 1 d) :=
    Ioo_mem_nhdsGT (lt_min one_pos hd)
  filter_upwards [hev] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hε1' : ε < 1 := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hεd : ε < d := lt_of_lt_of_le hε1 (min_le_right _ _)
  -- pointwise bound
  have hpt : ∀ t ∈ Set.uIoc ε d, ‖t ^ q * Lq A B C ε t‖ ≤ d ^ q * (c1 + |Real.log ε|) := by
    intro t ht
    rw [Set.uIoc_of_le hεd.le] at ht
    have hL := h.Lq_bound (s := ε) (t := t) (ρ := ε ^ 2) (R := 1 + d ^ 2) (by positivity)
      (by nlinarith [sq_nonneg t]) (by nlinarith [ht.2, ht.1])
    have hlog : |Real.log (ε ^ 2)| = 2 * |Real.log ε| := by
      rw [Real.log_pow]; push_cast; rw [abs_mul]; norm_num
    rw [hlog] at hL
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (lt_trans hε0 ht.1)]
    have hq : t ^ q ≤ d ^ q := pow_le_pow_left₀ (lt_trans hε0 ht.1).le ht.2 q
    have hLL : |Lq A B C ε t| ≤ c1 + |Real.log ε| := by
      refine hL.trans (le_of_eq ?_); rw [hc1]; ring
    exact mul_le_mul hq hLL (abs_nonneg _) (by positivity)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hε0]
  have hdε : |d - ε| ≤ d := by rw [abs_of_pos (by linarith)]; linarith
  have hnn : 0 ≤ d ^ q * (c1 + |Real.log ε|) := by
    have : 0 ≤ c1 := by rw [hc1]; positivity
    positivity
  have h2 : ‖∫ t in ε..d, t ^ q * Lq A B C ε t‖ ≤ d ^ q * (c1 + |Real.log ε|) * d :=
    hint.trans (mul_le_mul_of_nonneg_left hdε hnn)
  have hεp : ε ^ (p + 1) ≤ ε := by
    calc ε ^ (p + 1) ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le hε1'.le (by omega)
      _ = ε := pow_one ε
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hlogabs : |Real.log ε| = -Real.log ε := abs_of_neg (Real.log_neg hε0 hε1')
  calc ε ^ (p + 1) * ‖∫ t in ε..d, t ^ q * Lq A B C ε t‖
      ≤ ε * (d ^ q * (c1 + |Real.log ε|) * d) :=
        mul_le_mul hεp h2 (norm_nonneg _) hε0.le
    _ = F ε := by
        simp only [hF]
        have : |ε * Real.log ε| = ε * |Real.log ε| := by
          rw [abs_mul, abs_of_pos hε0]
        rw [this, pow_succ]
        ring

end CatalanCore.Uniform.Decay.Assembly
