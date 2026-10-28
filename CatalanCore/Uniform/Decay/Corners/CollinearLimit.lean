module

public import CatalanCore.Uniform.Decay.Corners.CollinearReg

@[expose] public section

/-!
# Collinear case `B² = A C`: the limit `δ → 0⁺`

`tendsto_BEL` (double integral), `edge_t_limit`, `edge_s_limit` (boundary integrals; the limit
integrands are interval integrable), all by dominated convergence with majorants built from
`|log (s + κ t)|`.
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory Filter Topology
open scoped ENNReal Interval
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

variable {A B C : ℝ}

theorem volume_rect_ne_top (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)) (Ioc a b ×ˢ Ioc c d) ≠ ∞ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem tendsto_BEL (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) (i j : ℕ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    Tendsto (fun δ : ℝ => BEL (A + δ) B (C + δ) i j a b c d) (𝓝[>] 0)
      (𝓝 (BEL A B C i j a b c d)) := by
  have hκ := kappa_ne_zero hA hC hB
  set S : ℝ := max |a| |b| with hS
  set T : ℝ := max |c| |d| with hT
  set κ : ℝ := B / A with hκdef
  set bound : ℝ × ℝ → ℝ := fun p =>
    S ^ i * T ^ j * (cR A B C (S ^ 2 + T ^ 2) + |Real.log (p.1 + κ * p.2)|) with hbound
  have hmeas : MeasurableSet (Ioc a b ×ˢ Ioc c d) := measurableSet_Ioc.prod measurableSet_Ioc
  have hbound_int : IntegrableOn bound (Ioc a b ×ˢ Ioc c d) := by
    have h1 := abslog_shear_integrableOn κ hab hcd
    have hc : IntegrableOn (fun _ : ℝ × ℝ => cR A B C (S ^ 2 + T ^ 2)) (Ioc a b ×ˢ Ioc c d) :=
      integrableOn_const (volume_rect_ne_top a b c d)
    exact (hc.add h1).const_mul _
  have hint0 : IntegrableOn (fun p : ℝ × ℝ => ff A B C i j p.1 p.2) (Ioc a b ×ˢ Ioc c d) := by
    refine Integrable.mono' hbound_int (measurable_ff A B C i j).aestronglyMeasurable ?_
    rw [ae_restrict_iff' hmeas]
    filter_upwards [ae_shear_ne κ hκ] with p hw hp
    have := ff_reg_bound hA hC hB i j (le_refl 0) zero_le_one hp hw
    simpa using this
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), BEL (A + δ) B (C + δ) i j a b c d
      = ∫ p in Ioc a b ×ˢ Ioc c d, ff (A + δ) B (C + δ) i j p.1 p.2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact BEL_eq_set (PD_reg hA hC hB hδ) i j hab hcd
  rw [BEL_eq_set' A B C i j hab hcd hint0]
  refine Tendsto.congr' (hev.mono fun δ h => h.symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall fun δ => (measurable_ff _ _ _ i j).aestronglyMeasurable) ?_
    hbound_int ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    rw [ae_restrict_iff' hmeas]
    filter_upwards [ae_shear_ne κ hκ] with p hw hp
    rw [Real.norm_eq_abs]
    exact ff_reg_bound hA hC hB i j hδ.1.le hδ.2.le hp hw
  · refine ae_restrict_of_ae ?_
    filter_upwards [ae_shear_ne κ hκ] with p hw
    exact (tendsto_Lq_reg hA hB hw).const_mul _

theorem edge_t_limit (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) (i j : ℕ) (e : ℝ) {c d : ℝ}
    (hcd : c ≤ d) :
    IntervalIntegrable (fun t => e ^ (i + 1) * t ^ j * Lq A B C e t) volume c d ∧
    Tendsto (fun δ : ℝ => ∫ t in c..d, e ^ (i + 1) * t ^ j * Lq (A + δ) B (C + δ) e t) (𝓝[>] 0)
      (𝓝 (∫ t in c..d, e ^ (i + 1) * t ^ j * Lq A B C e t)) := by
  have hκ := kappa_ne_zero hA hC hB
  set T : ℝ := max |c| |d| with hT
  set κ : ℝ := B / A with hκdef
  set bound : ℝ → ℝ := fun t =>
    |e| ^ (i + 1) * T ^ j * (cR A B C (e ^ 2 + T ^ 2) + |Real.log (e + κ * t)|) with hbound
  have hbound_int : IntervalIntegrable bound volume c d := by
    have h1 := abslog_affine_integrable e hκ c d
    exact (intervalIntegrable_const.add h1).const_mul _
  have hpt : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ t ∈ Ioc c d, e + κ * t ≠ 0 →
      ‖e ^ (i + 1) * t ^ j * Lq (A + δ) B (C + δ) e t‖ ≤ bound t := by
    intro δ h0 h1 t ht hw
    have ht' : |t| ≤ T := abs_le.2 ⟨by linarith [neg_abs_le c, le_max_left |c| |d|, le_abs_self (-c), ht.1],
      by linarith [le_abs_self d, le_max_right |c| |d|, ht.2]⟩
    have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    have hLL := Lq_reg_abs hA hC hB h0 h1 (R := e ^ 2 + T ^ 2) (s := e) (t := t) (by linarith) hw
    have hTj : |t| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg _) ht' j
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
    exact mul_le_mul (mul_le_mul le_rfl hTj (by positivity) (by positivity)) hLL (abs_nonneg _)
      (by positivity)
  have hmeasF : ∀ δ : ℝ, AEStronglyMeasurable
      (fun t => e ^ (i + 1) * t ^ j * Lq (A + δ) B (C + δ) e t) (volume.restrict (Ι c d)) := by
    intro δ
    refine Measurable.aestronglyMeasurable ?_
    unfold Lq qf; fun_prop
  have hnull : ∀ᵐ t : ℝ, e + κ * t ≠ 0 := by
    filter_upwards [(Set.countable_singleton (-e / κ)).ae_notMem (volume : Measure ℝ)] with t ht h
    apply ht
    rw [Set.mem_singleton_iff]
    field_simp
    linarith
  constructor
  · refine IntervalIntegrable.mono_fun' hbound_int (by simpa using hmeasF 0) ?_
    rw [uIoc_of_le hcd]
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hnull] with t hw ht
    have := hpt 0 le_rfl zero_le_one t ht hw
    simpa using this
  · refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
      (Filter.Eventually.of_forall hmeasF) ?_ hbound_int ?_
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
      filter_upwards [hnull] with t hw ht
      rw [uIoc_of_le hcd] at ht
      exact hpt δ hδ.1.le hδ.2.le t ht hw
    · filter_upwards [hnull] with t hw ht
      exact (tendsto_Lq_reg hA hB (s := e) (t := t) hw).const_mul _

theorem edge_s_limit (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) (i j : ℕ) (e : ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    IntervalIntegrable (fun s => s ^ i * e ^ (j + 1) * Lq A B C s e) volume a b ∧
    Tendsto (fun δ : ℝ => ∫ s in a..b, s ^ i * e ^ (j + 1) * Lq (A + δ) B (C + δ) s e) (𝓝[>] 0)
      (𝓝 (∫ s in a..b, s ^ i * e ^ (j + 1) * Lq A B C s e)) := by
  have hκ := kappa_ne_zero hA hC hB
  set S : ℝ := max |a| |b| with hS
  set κ : ℝ := B / A with hκdef
  set bound : ℝ → ℝ := fun s =>
    S ^ i * |e| ^ (j + 1) * (cR A B C (S ^ 2 + e ^ 2) + |Real.log (s + κ * e)|) with hbound
  have hbound_int : IntervalIntegrable bound volume a b := by
    have h1 : IntervalIntegrable (fun s : ℝ => |Real.log (s + κ * e)|) volume a b := by
      simpa [add_comm] using abslog_affine_integrable (κ * e) (κ := 1) one_ne_zero a b
    exact (intervalIntegrable_const.add h1).const_mul _
  have hpt : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ s ∈ Ioc a b, s + κ * e ≠ 0 →
      ‖s ^ i * e ^ (j + 1) * Lq (A + δ) B (C + δ) s e‖ ≤ bound s := by
    intro δ h0 h1 s hs hw
    have hs' : |s| ≤ S := abs_le.2 ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, le_abs_self (-a), hs.1],
      by linarith [le_abs_self b, le_max_right |a| |b|, hs.2]⟩
    have hs2 : s ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
    have hLL := Lq_reg_abs hA hC hB h0 h1 (R := S ^ 2 + e ^ 2) (s := s) (t := e) (by linarith) hw
    have hSi : |s| ^ i ≤ S ^ i := pow_le_pow_left₀ (abs_nonneg _) hs' i
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
    exact mul_le_mul (mul_le_mul hSi le_rfl (by positivity) (by positivity)) hLL (abs_nonneg _)
      (by positivity)
  have hmeasF : ∀ δ : ℝ, AEStronglyMeasurable
      (fun s => s ^ i * e ^ (j + 1) * Lq (A + δ) B (C + δ) s e) (volume.restrict (Ι a b)) := by
    intro δ
    refine Measurable.aestronglyMeasurable ?_
    unfold Lq qf; fun_prop
  have hnull : ∀ᵐ s : ℝ, s + κ * e ≠ 0 := by
    filter_upwards [(Set.countable_singleton (-(κ * e))).ae_notMem (volume : Measure ℝ)] with s hs h
    apply hs
    rw [Set.mem_singleton_iff]
    linarith
  constructor
  · refine IntervalIntegrable.mono_fun' hbound_int (by simpa using hmeasF 0) ?_
    rw [uIoc_of_le hab]
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hnull] with s hw hs
    have := hpt 0 le_rfl zero_le_one s hs hw
    simpa using this
  · refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
      (Filter.Eventually.of_forall hmeasF) ?_ hbound_int ?_
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
      filter_upwards [hnull] with s hw hs
      rw [uIoc_of_le hab] at hs
      exact hpt δ hδ.1.le hδ.2.le s hs hw
    · filter_upwards [hnull] with s hw hs
      exact (tendsto_Lq_reg hA hB (s := s) (t := e) hw).const_mul _

end CatalanCore.Uniform.Decay.Corners
