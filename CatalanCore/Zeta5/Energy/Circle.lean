module

public import CatalanCore.Zeta5.Energy.ZeroMass
public import CatalanCore.Zeta5.Energy.LayerCake
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/CircleAtoms.lean (Moritz Firsching); changes: module conversion, namespace CatalanCore.Zeta5.Energy; circles are now probability measures `circ c ε` on `ℂ` instead of curves (the integral over `[0, 2π]` carries the factor `(2π)⁻¹`), `circleMap_preimage_countable` is kept, the rest is new (ZD03, ZD06 integrability and distinctness). -/

/-!
# Circle measures and the integrability hypotheses of Lemma 6.2 (ZD03, ZD06)

* `circ c ε` : the uniform probability measure on the circle `|z - c| = ε`, `c ∈ ℝ`;
* `integral_log_circ` (ZD03) : `∫ log ‖z - a‖ d(circ c ε) = log ε + log⁺(ε⁻¹ ‖c - a‖)
  = log max(ε, ‖c - a‖)`, the circle average of the logarithm (Jensen);
* `nuC ν` : the push-forward of a measure on `ℝ` to `ℂ` along `ofReal`;
* `integrable_log_prod` : a uniform bound of `∫ |log ‖z - w‖| dμ(z)` over `w` gives integrability of
  `log ‖z - w‖` on `μ ⊗ ν`;
* `ae_ne_of_noAtoms` : atomless measures give a.e. distinctness `z ≠ w`.
-/

open MeasureTheory Set Real Filter Topology

namespace CatalanCore.Zeta5.Energy

/-- The uniform probability measure on the circle of radius `ε` about the real point `c`. -/
noncomputable def circ (c ε : ℝ) : Measure ℂ :=
  (ENNReal.ofReal (2 * π)⁻¹) • (volume.restrict (Ioc 0 (2 * π))).map (circleMap (c : ℂ) ε)

lemma measurable_circleMap' (c : ℂ) (ε : ℝ) : Measurable (circleMap c ε) :=
  (continuous_circleMap c ε).measurable

instance (c ε : ℝ) : IsProbabilityMeasure (circ c ε) := by
  refine ⟨?_⟩
  unfold circ
  rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap' _ _) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
    sub_zero, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  rw [inv_mul_cancel₀ (by positivity)]
  simp

lemma integral_circ (c ε : ℝ) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂(circ c ε) = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g (circleMap (c : ℂ) ε θ) := by
  unfold circ
  rw [integral_smul_measure, integral_map (measurable_circleMap' _ _).aemeasurable
    hg.aestronglyMeasurable, ← intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma ae_smul_measure' {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : α → Prop}
    (h : ∀ᵐ x ∂μ, p x) (c : ENNReal) : ∀ᵐ x ∂(c • μ), p x := by
  rw [ae_iff] at h ⊢
  rw [Measure.smul_apply, h, smul_zero]

lemma ae_norm_circ (c ε : ℝ) : ∀ᵐ z ∂(circ c ε), ‖z‖ ≤ |c| + |ε| := by
  unfold circ
  refine ae_smul_measure' ?_ _
  rw [ae_map_iff (measurable_circleMap' _ _).aemeasurable (measurableSet_le measurable_norm
    measurable_const)]
  refine ae_of_all _ fun θ => ?_
  have h1 : ‖circleMap (c : ℂ) ε θ‖ ≤ ‖circleMap (c : ℂ) ε θ - c‖ + ‖(c : ℂ)‖ := by
    calc ‖circleMap (c : ℂ) ε θ‖ = ‖(circleMap (c : ℂ) ε θ - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [circleMap_sub_center, norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

/-- Point preimages under `circleMap` are countable. -/
lemma circleMap_preimage_countable (c : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    (circleMap c R ⁻¹' {z}).Countable := by
  rcases (circleMap c R ⁻¹' {z}).eq_empty_or_nonempty with h | ⟨θ₀, hθ₀⟩
  · rw [h]; exact Set.countable_empty
  refine (Set.countable_range fun n : ℤ => θ₀ + n * (2 * π)).mono ?_
  intro θ hθ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, circleMap] at hθ hθ₀
  have he : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    have := hθ.trans hθ₀.symm
    have h2 : (R : ℂ) * Complex.exp (θ * Complex.I) = R * Complex.exp (θ₀ * Complex.I) := by
      linear_combination this
    exact mul_left_cancel₀ hR' h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨n, ?_⟩
  have : (θ : ℂ) = θ₀ + n * (2 * π) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h3 : (θ : ℂ) * Complex.I = (θ₀ + n * (2 * π)) * Complex.I := by
      rw [hn]; ring
    exact mul_right_cancel₀ hI h3
  exact_mod_cast this.symm

lemma circ_singleton (c : ℝ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) : circ c ε {z} = 0 := by
  unfold circ
  rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap' _ _) (measurableSet_singleton z)]
  have h0 : volume (circleMap (c : ℂ) ε ⁻¹' {z}) = 0 :=
    (circleMap_preimage_countable _ hε z).measure_zero _
  have : (volume.restrict (Ioc 0 (2 * π))) (circleMap (c : ℂ) ε ⁻¹' {z}) = 0 :=
    le_antisymm ((Measure.restrict_le_self _).trans h0.le) bot_le
  rw [this, smul_zero]

/-- **ZD03**: the circle average of the logarithm, `∫ log ‖z - a‖ d(circ c ε) = log ε + log⁺(ε⁻¹‖c - a‖)`. -/
theorem integral_log_circ (c : ℝ) {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    ∫ z, Real.log ‖z - a‖ ∂(circ c ε) = Real.log ε + Real.posLog (ε⁻¹ * ‖(c : ℂ) - a‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := (c : ℂ))
    hε.ne'
  rw [circleAverage_def, smul_eq_mul] at h
  rw [integral_circ c ε (by fun_prop)]
  exact h

lemma log_max_eq {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    Real.log ε + Real.posLog (ε⁻¹ * x) = Real.log (max ε x) := by
  rcases le_total x ε with h | h
  · rw [max_eq_left h, (Real.posLog_eq_zero_iff _).mpr (by
      rw [abs_of_nonneg (by positivity)]
      calc ε⁻¹ * x ≤ ε⁻¹ * ε := by gcongr
        _ = 1 := inv_mul_cancel₀ hε.ne'), add_zero]
  · rw [max_eq_right h, Real.posLog_eq_log (by
      rw [abs_of_nonneg (by positivity)]
      calc (1 : ℝ) = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
        _ ≤ ε⁻¹ * x := by gcongr),
      Real.log_mul (inv_ne_zero hε.ne') (by
        rcases hx.eq_or_lt with h0 | h0
        · exfalso; rw [← h0] at h; linarith
        · exact h0.ne'), Real.log_inv]
    ring

lemma integral_log_circ_max (c : ℝ) {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    ∫ z, Real.log ‖z - a‖ ∂(circ c ε) = Real.log (max ε ‖(c : ℂ) - a‖) := by
  rw [integral_log_circ c hε a, log_max_eq hε (norm_nonneg _)]

lemma integrable_log_circ (c : ℝ) {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖) (circ c ε) := by
  have h1 : IntervalIntegrable (fun θ => Real.log ‖circleMap (c : ℂ) ε θ - a‖) volume 0 (2 * π) :=
    circleIntegrable_log_norm_sub_const ε
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at h1
  unfold circ
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  exact (integrable_map_measure (Real.measurable_log.comp (measurable_norm.comp
    (measurable_id.sub measurable_const))).aestronglyMeasurable
    (measurable_circleMap' _ _).aemeasurable).mpr h1

/-- Uniform bound for the absolute logarithmic potential of a circle at a point of norm `≤ A`. -/
lemma integral_abs_log_circ_le (c : ℝ) {ε : ℝ} (hε : 0 < ε) {A : ℝ} (a : ℂ) (ha : ‖a‖ ≤ A) :
    ∫ z, |Real.log ‖z - a‖| ∂(circ c ε) ≤ 2 * Real.log (1 + |c| + ε + A) + |Real.log ε| := by
  have hpos : ∀ z : ℂ, |Real.log ‖z - a‖| = 2 * Real.posLog ‖z - a‖ - Real.log ‖z - a‖ := by
    intro z
    have := Real.half_mul_log_add_log_abs (x := ‖z - a‖)
    linarith
  have hint1 : Integrable (fun z : ℂ => Real.posLog ‖z - a‖) (circ c ε) := by
    refine Integrable.mono' (integrable_const (Real.log (1 + |c| + ε + A)))
      (by
        have : Measurable fun z : ℂ => Real.posLog ‖z - a‖ := by
          show Measurable fun z : ℂ => max 0 (Real.log ‖z - a‖)
          exact measurable_const.max (by fun_prop)
        exact this.aestronglyMeasurable) ?_
    filter_upwards [ae_norm_circ c ε] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg Real.posLog_nonneg]
    have h1 : ‖z - a‖ ≤ |c| + ε + A := by
      calc ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ |c| + |ε| + A := by linarith
        _ = |c| + ε + A := by rw [abs_of_pos hε]
    calc Real.posLog ‖z - a‖ ≤ Real.log (1 + ‖z - a‖) :=
          Real.posLog_le_log_one_add (norm_nonneg _)
      _ ≤ Real.log (1 + |c| + ε + A) :=
          Real.log_le_log (by positivity) (by linarith)
  have hint2 := integrable_log_circ c hε a
  simp_rw [hpos]
  rw [integral_sub (hint1.const_mul 2) hint2, integral_const_mul, integral_log_circ c hε a]
  have hle : ∫ z, Real.posLog ‖z - a‖ ∂(circ c ε) ≤ Real.log (1 + |c| + ε + A) := by
    have := integral_mono_ae (μ := circ c ε) (f := fun z : ℂ => Real.posLog ‖z - a‖)
      (g := fun _ => Real.log (1 + |c| + ε + A)) hint1 (integrable_const _) (by
        filter_upwards [ae_norm_circ c ε] with z hz
        have h1 : ‖z - a‖ ≤ |c| + ε + A := by
          calc ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le _ _
            _ ≤ |c| + |ε| + A := by linarith
            _ = |c| + ε + A := by rw [abs_of_pos hε]
        calc Real.posLog ‖z - a‖ ≤ Real.log (1 + ‖z - a‖) :=
              Real.posLog_le_log_one_add (norm_nonneg _)
          _ ≤ Real.log (1 + |c| + ε + A) :=
              Real.log_le_log (by positivity) (by linarith))
    simpa using this
  have h2 : 0 ≤ Real.posLog (ε⁻¹ * ‖(c : ℂ) - a‖) := Real.posLog_nonneg
  have h3 : -Real.log ε ≤ |Real.log ε| := neg_le_abs _
  linarith

/-! ### Real measures pushed into `ℂ` -/

lemma measurableEmbedding_ofReal : MeasurableEmbedding (fun x : ℝ => (x : ℂ)) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

/-- The push-forward of a measure on `ℝ` along `ofReal`. -/
noncomputable def nuC (ν : Measure ℝ) : Measure ℂ := ν.map (fun x : ℝ => (x : ℂ))

instance (ν : Measure ℝ) [IsFiniteMeasure ν] : IsFiniteMeasure (nuC ν) := by
  unfold nuC; infer_instance

lemma integral_nuC (ν : Measure ℝ) (g : ℂ → ℝ) :
    ∫ z, g z ∂(nuC ν) = ∫ u, g (u : ℂ) ∂ν :=
  measurableEmbedding_ofReal.integral_map g

lemma nuC_real_univ (ν : Measure ℝ) : (nuC ν).real univ = ν.real univ := by
  simp only [Measure.real, nuC]
  rw [Measure.map_apply measurableEmbedding_ofReal.measurable MeasurableSet.univ, preimage_univ]

lemma ae_nuC (ν : Measure ℝ) {p : ℂ → Prop} :
    Filter.Eventually (fun z => p z) (ae (nuC ν)) ↔
      Filter.Eventually (fun u : ℝ => p (u : ℂ)) (ae ν) :=
  measurableEmbedding_ofReal.ae_map_iff

lemma nuC_singleton {ν : Measure ℝ} (h : ∀ x, ν {x} = 0) (z : ℂ) : nuC ν {z} = 0 := by
  unfold nuC
  rw [Measure.map_apply measurableEmbedding_ofReal.measurable (measurableSet_singleton z)]
  by_cases hz : ∃ x : ℝ, (x : ℂ) = z
  · obtain ⟨x, rfl⟩ := hz
    refine measure_mono_null (fun y hy => ?_) (h x)
    simp only [mem_preimage, mem_singleton_iff] at hy
    exact (Complex.ofReal_injective hy)
  · push Not at hz
    have : (fun x : ℝ => (x : ℂ)) ⁻¹' {z} = ∅ := by
      ext y; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact hz y
    rw [this]; simp

lemma ae_norm_nuC {ν : Measure ℝ} {b F : ℝ} (h : ArcMaj ν b F) : ∀ᵐ z ∂(nuC ν), ‖z‖ ≤ b := by
  rw [ae_nuC]
  filter_upwards [h.ae_mem] with u hu
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact hu.2

/-! ### Integrability of the logarithmic kernel on products -/

section Products

variable {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma integrable_log_prod {C : ℝ}
    (hi : ∀ᵐ w ∂ν, Integrable (fun z : ℂ => Real.log ‖z - w‖) μ)
    (hb : ∀ᵐ w ∂ν, ∫ z, |Real.log ‖z - w‖| ∂μ ≤ C) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν) :=
    (Real.measurable_log.comp (measurable_norm.comp
      (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨hi, ?_⟩
  refine Integrable.mono' (integrable_const |C|) ?_ ?_
  · have hg : Measurable fun p : ℂ × ℂ => ‖Real.log ‖p.2 - p.1‖‖ :=
      (Real.measurable_log.comp (measurable_norm.comp
        (measurable_snd.sub measurable_fst))).norm
    exact hg.aestronglyMeasurable.integral_prod_right' (μ := ν) (ν := μ)
  · filter_upwards [hb] with w hw
    rw [Real.norm_eq_abs]
    have : 0 ≤ ∫ z, ‖Real.log ‖z - w‖‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    rw [abs_of_nonneg this]
    simp only [Real.norm_eq_abs]
    exact hw.trans (le_abs_self C)

lemma integrable_log_swap
    (h : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν)) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (ν.prod μ) := by
  have := h.swap
  refine this.congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]

lemma ae_ne_of_noAtoms_right (h : ∀ z, ν {z} = 0) : ∀ᵐ p ∂(μ.prod ν), p.1 ≠ p.2 := by
  have hs : MeasurableSet {p : ℂ × ℂ | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (μ := μ) (ν := ν) hs).mpr (ae_of_all _ fun x => ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (h x)] with y hy hxy
  exact hy (by simp [hxy])

lemma ae_ne_of_noAtoms_left (h : ∀ z, μ {z} = 0) : ∀ᵐ p ∂(μ.prod ν), p.1 ≠ p.2 := by
  have h2 := ae_ne_of_noAtoms_right (μ := ν) (ν := μ) h
  have := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae h2
  filter_upwards [this] with p hp
  exact fun e => hp e.symm

end Products

end CatalanCore.Zeta5.Energy
