module

public import CatalanCore.Uniform.Decay.Corners.CollinearBound

@[expose] public section

/-!
# Collinear case `B² = A C`: the regularised forms `(A+δ, B, C+δ)` and the double integral

For `δ > 0` the form `(A+δ, B, C+δ)` is positive definite (`B² = AC < (A+δ)(C+δ)`), so
`BE_pd` applies.  This module proves the `δ → 0⁺` limit of the double integral `BEL`
(`tendsto_BEL`) by dominated convergence with majorant `S^i T^j (c + |log (s + κ t)|)`.
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory Filter Topology
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

variable {A B C : ℝ}

theorem qf_upper (hA : 0 < A) (hC : 0 < C) (s t : ℝ) :
    qf A B C s t ≤ (A + C + |B|) * (s ^ 2 + t ^ 2) := by
  unfold qf
  have h1 : 2 * B * s * t ≤ |B| * (s ^ 2 + t ^ 2) := by
    have : 2 * B * s * t ≤ 2 * |B| * |s| * |t| := by
      calc 2 * B * s * t = 2 * (B * s * t) := by ring
        _ ≤ 2 * |B * s * t| := by linarith [le_abs_self (B * s * t)]
        _ = 2 * |B| * |s| * |t| := by rw [abs_mul, abs_mul]; ring
    nlinarith [sq_abs s, sq_abs t, sq_nonneg (|s| - |t|), abs_nonneg B]
  nlinarith [sq_nonneg s, sq_nonneg t, abs_nonneg B]

theorem qf_reg (A B C δ s t : ℝ) :
    qf (A + δ) B (C + δ) s t = qf A B C s t + δ * (s ^ 2 + t ^ 2) := by
  unfold qf; ring

theorem PD_reg (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) {δ : ℝ} (hδ : 0 < δ) :
    PD (A + δ) B (C + δ) (((A + δ) * (C + δ) - B ^ 2) / ((A + δ) + (C + δ)))
      ((A + δ) + (C + δ) + |B|) :=
  PD.of_posdef (by linarith) (by linarith) (by nlinarith [mul_pos hA hC])

theorem reg_bounds (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) {δ : ℝ} (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1) {R s t : ℝ} (hR : s ^ 2 + t ^ 2 ≤ R) :
    A * (s + B / A * t) ^ 2 ≤ qf (A + δ) B (C + δ) s t ∧
      qf (A + δ) B (C + δ) s t ≤ (A + C + |B| + 2) * R := by
  rw [qf_reg, qf_collinear hA hB]
  have hr : 0 ≤ s ^ 2 + t ^ 2 := by positivity
  constructor
  · nlinarith [mul_nonneg h0 hr]
  · have := qf_upper (B := B) hA hC s t
    rw [qf_collinear hA hB] at this
    have hK : 0 ≤ A + C + |B| + 2 := by positivity
    nlinarith [mul_nonneg h0 hr, mul_nonneg hK (sub_nonneg.2 hR), abs_nonneg B,
      mul_le_mul_of_nonneg_right h1 hr]

/-- Majorant constant. -/
noncomputable def cR (A B C R : ℝ) : ℝ := (|Real.log A| + |Real.log ((A + C + |B| + 2) * R)|) / 2

theorem Lq_reg_abs (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) {δ : ℝ} (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1) {R s t : ℝ} (hR : s ^ 2 + t ^ 2 ≤ R) (hw : s + B / A * t ≠ 0) :
    |Lq (A + δ) B (C + δ) s t| ≤ cR A B C R + |Real.log (s + B / A * t)| := by
  obtain ⟨hl, hu⟩ := reg_bounds hA hC hB h0 h1 hR
  exact Lq_reg_bound hA hw hl hu

theorem tendsto_Lq_reg (hA : 0 < A) (hB : B ^ 2 = A * C) {s t : ℝ} (hw : s + B / A * t ≠ 0) :
    Tendsto (fun δ : ℝ => Lq (A + δ) B (C + δ) s t) (𝓝[>] 0) (𝓝 (Lq A B C s t)) := by
  have hq : 0 < qf A B C s t := by
    rw [qf_collinear hA hB]; positivity
  have hc : ContinuousAt (fun δ : ℝ => Real.log (qf (A + δ) B (C + δ) s t) / 2) 0 := by
    have h1 : Continuous fun δ : ℝ => qf (A + δ) B (C + δ) s t := by unfold qf; fun_prop
    have h2 : qf (A + 0) B (C + 0) s t ≠ 0 := by simpa using hq.ne'
    exact (ContinuousAt.log h1.continuousAt h2).div_const 2
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [Lq] using this

theorem ae_shear_ne (κ : ℝ) (hκ : κ ≠ 0) :
    ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), p.1 + κ * p.2 ≠ 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 + κ * p.2 ≠ 0} :=
    (measurableSet_singleton (0 : ℝ)).compl.preimage (by fun_prop)
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hm]
  refine Filter.Eventually.of_forall fun x => ?_
  filter_upwards [(Set.countable_singleton (-x / κ)).ae_notMem (volume : Measure ℝ)] with y hy h
  apply hy
  rw [Set.mem_singleton_iff]
  field_simp
  linarith

/-- Fubini form of `BEL` given integrability of the integrand. -/
theorem BEL_eq_set' (A B C : ℝ) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hI : IntegrableOn (fun p : ℝ × ℝ => ff A B C i j p.1 p.2) (Ioc a b ×ˢ Ioc c d)) :
    BEL A B C i j a b c d = ∫ p in Ioc a b ×ˢ Ioc c d, ff A B C i j p.1 p.2 := by
  rw [Measure.volume_eq_prod] at hI ⊢
  rw [setIntegral_prod _ hI]
  unfold BEL
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  simp only [ff]
  rw [intervalIntegral.integral_of_le hcd]

theorem ff_reg_bound (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) (i j : ℕ) {δ : ℝ} (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1) {a b c d : ℝ} {p : ℝ × ℝ} (hp : p ∈ Ioc a b ×ˢ Ioc c d)
    (hw : p.1 + B / A * p.2 ≠ 0) :
    |ff (A + δ) B (C + δ) i j p.1 p.2| ≤
      (max |a| |b|) ^ i * (max |c| |d|) ^ j *
        (cR A B C ((max |a| |b|) ^ 2 + (max |c| |d|) ^ 2) + |Real.log (p.1 + B / A * p.2)|) := by
  obtain ⟨⟨hp1a, hp1b⟩, ⟨hp2c, hp2d⟩⟩ := hp
  set S : ℝ := max |a| |b| with hS
  set T : ℝ := max |c| |d| with hT
  have hs : |p.1| ≤ S := abs_le.2 ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, le_abs_self (-a)],
    by linarith [le_abs_self b, le_max_right |a| |b|]⟩
  have ht : |p.2| ≤ T := abs_le.2 ⟨by linarith [neg_abs_le c, le_max_left |c| |d|, le_abs_self (-c)],
    by linarith [le_abs_self d, le_max_right |c| |d|]⟩
  have hs2 : p.1 ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs p.1, abs_nonneg p.1]
  have ht2 : p.2 ^ 2 ≤ T ^ 2 := by nlinarith [sq_abs p.2, abs_nonneg p.2]
  have hLL := Lq_reg_abs hA hC hB h0 h1 (R := S ^ 2 + T ^ 2) (s := p.1) (t := p.2)
    (by linarith) hw
  have hSi : |p.1| ^ i ≤ S ^ i := pow_le_pow_left₀ (abs_nonneg _) hs i
  have hTj : |p.2| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg _) ht j
  unfold ff
  rw [abs_mul, abs_mul, abs_pow, abs_pow]
  exact mul_le_mul (mul_le_mul hSi hTj (by positivity) (by positivity)) hLL (abs_nonneg _)
    (by positivity)

end CatalanCore.Uniform.Decay.Corners
