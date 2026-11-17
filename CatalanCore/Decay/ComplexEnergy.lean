module

public import CatalanCore.Zeta5.Energy.Config
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# The energy layer for configurations of complex points (Lai decay, LD06, LD07, LD09)

Generic in a finite measure `σ` on `ℂ` (the dual measure) and in the configuration.  Sign
convention: `potC σ t = ∫ log ‖t - u‖ dσ(u)` and `energyC σ = ∬ log ‖u - v‖ dσ dσ`, so the paper's
`U^σ` is `-potC σ` and the paper's `I(σ)` is `-energyC σ`.

* `circZ c ε` (`c : ℂ`): the uniform probability measure on the circle of radius `ε` about `c`.
  This generalises `Zeta5.Energy.circ` (real centre) by a NEW module beside it.
* `BallMaj σ b A` (LD07): support in the closed ball of radius `b`, and `σ(B(c, r)) ≤ A r` for all
  centres and radii.  It holds for a finite sum of bounded line densities on segments.
  Under `BallMaj`, `∫ log⁺(ε / ‖c - u‖) dσ(u) ≤ A ε` (`integral_regC_le`), i.e. the smoothed
  potential differs from `potC σ` by at most `A ε`.
* `energy_rawC` (LD06 + LD07): the configuration inequality at complex points
  `h log ε + ∑ᵢ ∑ᵢ' log ‖tᵢ - tᵢ'‖ ≤ 2K ∑ᵢ (potC σ tᵢ + A ε) - K² energyC σ`, `h = K σ(ℂ)`.
* `complex_bound` (LD09): the integral form, for any σ-finite weight space.
-/

open MeasureTheory Set Real Filter Topology CatalanCore.Zeta5.Energy

namespace CatalanCore.Decay.ComplexEnergy

/-! ### Circles about complex centres -/

/-- The uniform probability measure on the circle of radius `ε` about the complex point `c`. -/
noncomputable def circZ (c : ℂ) (ε : ℝ) : Measure ℂ :=
  (ENNReal.ofReal (2 * π)⁻¹) • (volume.restrict (Ioc 0 (2 * π))).map (circleMap c ε)

instance (c : ℂ) (ε : ℝ) : IsProbabilityMeasure (circZ c ε) := by
  refine ⟨?_⟩
  unfold circZ
  rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap' _ _) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
    sub_zero, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  rw [inv_mul_cancel₀ (by positivity)]
  simp

lemma integral_circZ (c : ℂ) (ε : ℝ) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂(circZ c ε) = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g (circleMap c ε θ) := by
  unfold circZ
  rw [integral_smul_measure, integral_map (measurable_circleMap' _ _).aemeasurable
    hg.aestronglyMeasurable, ← intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma ae_norm_circZ (c : ℂ) (ε : ℝ) : ∀ᵐ z ∂(circZ c ε), ‖z‖ ≤ ‖c‖ + |ε| := by
  unfold circZ
  refine ae_smul_measure' ?_ _
  rw [ae_map_iff (measurable_circleMap' _ _).aemeasurable (measurableSet_le measurable_norm
    measurable_const)]
  refine ae_of_all _ fun θ => ?_
  have h1 : ‖circleMap c ε θ‖ ≤ ‖circleMap c ε θ - c‖ + ‖c‖ := by
    calc ‖circleMap c ε θ‖ = ‖(circleMap c ε θ - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [circleMap_sub_center, norm_circleMap_zero] at h1
  linarith

lemma ae_dist_circZ (c : ℂ) {ε : ℝ} (hε : 0 < ε) : ∀ᵐ w ∂(circZ c ε), ‖c - w‖ = ε := by
  unfold circZ
  refine ae_smul_measure' ?_ _
  rw [ae_map_iff (measurable_circleMap' _ _).aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine ae_of_all _ fun θ => ?_
  rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]

lemma circZ_singleton (c : ℂ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) : circZ c ε {z} = 0 := by
  unfold circZ
  rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap' _ _) (measurableSet_singleton z)]
  have h0 : volume (circleMap c ε ⁻¹' {z}) = 0 :=
    (circleMap_preimage_countable _ hε z).measure_zero _
  have : (volume.restrict (Ioc 0 (2 * π))) (circleMap c ε ⁻¹' {z}) = 0 :=
    le_antisymm ((Measure.restrict_le_self _).trans h0.le) bot_le
  rw [this, smul_zero]

/-- **LD06**: the circle average of the logarithm about a COMPLEX centre,
`∫ log ‖z - a‖ d(circZ c ε) = log (max ε ‖c - a‖)`. -/
theorem integral_log_circZ (c : ℂ) {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    ∫ z, Real.log ‖z - a‖ ∂(circZ c ε) = Real.log ε + Real.posLog (ε⁻¹ * ‖c - a‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := c) hε.ne'
  rw [circleAverage_def, smul_eq_mul] at h
  rw [integral_circZ c ε (by fun_prop)]
  exact h

lemma integral_log_circZ_max (c : ℂ) {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    ∫ z, Real.log ‖z - a‖ ∂(circZ c ε) = Real.log (max ε ‖c - a‖) := by
  rw [integral_log_circZ c hε a, log_max_eq hε (norm_nonneg _)]

lemma integrable_log_circZ (c : ℂ) {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖) (circZ c ε) := by
  have h1 : IntervalIntegrable (fun θ => Real.log ‖circleMap c ε θ - a‖) volume 0 (2 * π) :=
    circleIntegrable_log_norm_sub_const ε
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at h1
  unfold circZ
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  exact (integrable_map_measure (Real.measurable_log.comp (measurable_norm.comp
    (measurable_id.sub measurable_const))).aestronglyMeasurable
    (measurable_circleMap' _ _).aemeasurable).mpr h1

lemma integral_abs_log_circZ_le (c : ℂ) {ε : ℝ} (hε : 0 < ε) {A : ℝ} (a : ℂ) (ha : ‖a‖ ≤ A) :
    ∫ z, |Real.log ‖z - a‖| ∂(circZ c ε) ≤ 2 * Real.log (1 + ‖c‖ + ε + A) + |Real.log ε| := by
  have hpos : ∀ z : ℂ, |Real.log ‖z - a‖| = 2 * Real.posLog ‖z - a‖ - Real.log ‖z - a‖ := by
    intro z
    have := Real.half_mul_log_add_log_abs (x := ‖z - a‖)
    linarith
  have hb : ∀ᵐ z ∂(circZ c ε), Real.posLog ‖z - a‖ ≤ Real.log (1 + ‖c‖ + ε + A) := by
    filter_upwards [ae_norm_circZ c ε] with z hz
    have h1 : ‖z - a‖ ≤ ‖c‖ + ε + A := by
      calc ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ ‖c‖ + |ε| + A := by linarith
        _ = ‖c‖ + ε + A := by rw [abs_of_pos hε]
    calc Real.posLog ‖z - a‖ ≤ Real.log (1 + ‖z - a‖) :=
          Real.posLog_le_log_one_add (norm_nonneg _)
      _ ≤ Real.log (1 + ‖c‖ + ε + A) :=
          Real.log_le_log (by positivity) (by linarith)
  have hint1 : Integrable (fun z : ℂ => Real.posLog ‖z - a‖) (circZ c ε) := by
    refine Integrable.mono' (integrable_const (Real.log (1 + ‖c‖ + ε + A)))
      (by
        have : Measurable fun z : ℂ => Real.posLog ‖z - a‖ := by
          show Measurable fun z : ℂ => max 0 (Real.log ‖z - a‖)
          exact measurable_const.max (by fun_prop)
        exact this.aestronglyMeasurable) ?_
    filter_upwards [hb] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg Real.posLog_nonneg]
    exact hz
  have hint2 := integrable_log_circZ c hε a
  simp_rw [hpos]
  rw [integral_sub (hint1.const_mul 2) hint2, integral_const_mul, integral_log_circZ c hε a]
  have hle : ∫ z, Real.posLog ‖z - a‖ ∂(circZ c ε) ≤ Real.log (1 + ‖c‖ + ε + A) := by
    have := integral_mono_ae (μ := circZ c ε) (f := fun z : ℂ => Real.posLog ‖z - a‖)
      (g := fun _ => Real.log (1 + ‖c‖ + ε + A)) hint1 (integrable_const _) hb
    simpa using this
  have h2 : 0 ≤ Real.posLog (ε⁻¹ * ‖c - a‖) := Real.posLog_nonneg
  have h3 : -Real.log ε ≤ |Real.log ε| := neg_le_abs _
  linarith

/-! ### The dual measure: `BallMaj` and the regularisation estimate (LD07) -/

/-- Hypotheses on a measure `σ` on `ℂ` used by the circle regularisation: support in the closed
ball of radius `b` about 0, and Hölder growth `σ(B(c, r)) ≤ A r^α` of ball masses (`α > 0`). -/
structure BallMajA (σ : Measure ℂ) (b A α : ℝ) : Prop where
  b_pos : 0 < b
  A_nonneg : 0 ≤ A
  α_pos : 0 < α
  supp : σ (Metric.closedBall (0 : ℂ) b)ᶜ = 0
  maj : ∀ (c : ℂ) (r : ℝ), 0 ≤ r → σ (Metric.closedBall c r) ≤ ENNReal.ofReal (A * r ^ α)

/-- The linear case `α = 1`: `σ(B(c, r)) ≤ A r`. -/
abbrev BallMaj (σ : Measure ℂ) (b A : ℝ) : Prop := BallMajA σ b A 1

variable {σ : Measure ℂ} {b A α : ℝ}

namespace BallMajA

lemma ae_mem (h : BallMajA σ b A α) : ∀ᵐ u ∂σ, ‖u‖ ≤ b := by
  have := measure_eq_zero_iff_ae_notMem.mp h.supp
  filter_upwards [this] with u hu
  simpa using hu

/-- `σ` has no atoms. -/
lemma singleton_zero (h : BallMajA σ b A α) (x : ℂ) : σ {x} = 0 := by
  refine le_antisymm ?_ bot_le
  have h1 : σ {x} ≤ σ (Metric.closedBall x 0) := by
    apply measure_mono
    intro y hy
    rw [mem_singleton_iff] at hy
    subst hy
    simp
  refine h1.trans ((h.maj x 0 le_rfl).trans ?_)
  rw [Real.zero_rpow h.α_pos.ne', mul_zero]
  simp

end BallMajA

/-- The regularisation integrand `log⁺(ε/‖t - u‖)`. -/
noncomputable def regC (t : ℂ) (ε : ℝ) (u : ℂ) : ℝ := Real.posLog (ε / ‖t - u‖)

lemma measurable_regC (t : ℂ) (ε : ℝ) : Measurable (regC t ε) := by
  have : Measurable fun u : ℂ => ε / ‖t - u‖ := by fun_prop
  show Measurable fun u => max 0 (Real.log (ε / ‖t - u‖))
  exact measurable_const.max (Real.measurable_log.comp this)

lemma regC_nonneg (t : ℂ) (ε : ℝ) (u : ℂ) : 0 ≤ regC t ε u := Real.posLog_nonneg

/-- The level sets of `regC` lie in balls. -/
lemma regC_level {t : ℂ} {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 0 < s) {u : ℂ}
    (hu : s < regC t ε u) : u ∈ Metric.closedBall t (ε * Real.exp (-s)) := by
  unfold regC at hu
  rw [Real.posLog_apply] at hu
  have hlog : s < Real.log (ε / ‖t - u‖) := by
    rcases lt_max_iff.mp hu with h | h
    · exact absurd h (not_lt.mpr hs.le)
    · exact h
  have hx : 0 < ε / ‖t - u‖ := by
    by_contra hx
    have hx0 : ε / ‖t - u‖ = 0 := le_antisymm (not_lt.mp hx) (by positivity)
    rw [hx0, Real.log_zero] at hlog
    linarith
  have hd : 0 < ‖t - u‖ := by
    by_contra hd
    have : ‖t - u‖ = 0 := le_antisymm (not_lt.mp hd) (norm_nonneg _)
    rw [this, div_zero] at hx
    exact lt_irrefl _ hx
  have h2 : Real.exp s < ε / ‖t - u‖ := (Real.lt_log_iff_exp_lt hx).mp hlog
  rw [lt_div_iff₀ hd] at h2
  have h3 : ‖t - u‖ < ε * Real.exp (-s) := by
    have hes : 0 < Real.exp s := Real.exp_pos s
    rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ hes]
    linarith
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact h3.le

/-- **LD07** in `lintegral` form: `∫ log⁺(ε/‖t - u‖) dσ ≤ A ε^α / α`. -/
lemma lintegral_regC_le (hσ : BallMajA σ b A α) {ε : ℝ} (hε : 0 < ε) (t : ℂ) :
    ∫⁻ u, ENNReal.ofReal (regC t ε u) ∂σ ≤ ENNReal.ofReal (A * ε ^ α / α) := by
  rw [lintegral_eq_lintegral_meas_lt σ (ae_of_all _ fun u => regC_nonneg t ε u)
    (measurable_regC t ε).aemeasurable]
  set C : ℝ := A * ε ^ α with hC
  have hC0 : 0 ≤ C := mul_nonneg hσ.A_nonneg (Real.rpow_nonneg hε.le _)
  have hpt : ∀ s ∈ Ioi (0 : ℝ), σ {a | s < regC t ε a} ≤
      ENNReal.ofReal (C * Real.exp (-α * s)) := by
    intro s hs
    have hs : 0 < s := hs
    refine (measure_mono fun u hu => regC_level hε hs hu).trans ?_
    refine (hσ.maj t (ε * Real.exp (-s)) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.mul_rpow hε.le (Real.exp_pos _).le, ← Real.exp_mul, hC]
    refine le_of_eq ?_
    rw [← mul_assoc]; ring_nf
  have hint : IntegrableOn (fun s : ℝ => C * Real.exp (-α * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith [hσ.α_pos]) 0).const_mul C
  calc ∫⁻ s in Ioi 0, σ {a | s < regC t ε a}
      ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal (C * Real.exp (-α * s)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (∫ s in Ioi 0, C * Real.exp (-α * s)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun s => by positivity)).symm
    _ = ENNReal.ofReal (A * ε ^ α / α) := by
        congr 1
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [hσ.α_pos])]
        simp only [mul_zero, Real.exp_zero]
        rw [hC]
        field_simp [hσ.α_pos.ne']

lemma integrable_regC (hσ : BallMajA σ b A α) [IsFiniteMeasure σ] {ε : ℝ} (hε : 0 < ε) (t : ℂ) :
    Integrable (regC t ε) σ := by
  refine ⟨(measurable_regC t ε).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => regC_nonneg t ε u)]
  exact (lintegral_regC_le hσ hε t).trans_lt ENNReal.ofReal_lt_top

/-- **LD07**: `∫ log⁺(ε/‖t - u‖) dσ(u) ≤ A ε^α / α` for every `t ∈ ℂ`. -/
theorem integral_regC_le (hσ : BallMajA σ b A α) [IsFiniteMeasure σ] {ε : ℝ} (hε : 0 < ε) (t : ℂ) :
    ∫ u, regC t ε u ∂σ ≤ A * ε ^ α / α := by
  have h := lintegral_regC_le hσ hε t
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_regC hσ hε t)
    (ae_of_all _ fun u => regC_nonneg t ε u)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by have := hσ.A_nonneg; have := hσ.α_pos; positivity)).mp h

/-- The part `log⁺‖t - u‖`. -/
noncomputable def posC (t u : ℂ) : ℝ := Real.posLog ‖t - u‖

lemma measurable_posC (t : ℂ) : Measurable (posC t) := by
  have : Measurable fun u : ℂ => ‖t - u‖ := by fun_prop
  show Measurable fun u => max 0 (Real.log ‖t - u‖)
  exact measurable_const.max (Real.measurable_log.comp this)

lemma posC_le (hσ : BallMajA σ b A α) (t : ℂ) :
    ∀ᵐ u ∂σ, posC t u ≤ Real.log (1 + ‖t‖ + b) := by
  filter_upwards [hσ.ae_mem] with u hu
  have h1 : ‖t - u‖ ≤ ‖t‖ + b := (norm_sub_le _ _).trans (by linarith)
  have h2 : Real.posLog ‖t - u‖ ≤ Real.posLog (‖t‖ + b) :=
    Real.posLog_le_posLog (by linarith [norm_nonneg (t - u)]) h1
  have h3 : Real.posLog (‖t‖ + b) ≤ Real.log (1 + (‖t‖ + b)) :=
    Real.posLog_le_log_one_add (by linarith [norm_nonneg t, hσ.b_pos])
  unfold posC
  calc _ ≤ _ := h2.trans h3
    _ = _ := by ring_nf

lemma integrable_posC (hσ : BallMajA σ b A α) [IsFiniteMeasure σ] (t : ℂ) :
    Integrable (posC t) σ := by
  refine Integrable.mono' (integrable_const (Real.log (1 + ‖t‖ + b)))
    (measurable_posC t).aestronglyMeasurable ?_
  filter_upwards [posC_le hσ t] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ posC t u from Real.posLog_nonneg)]
  exact hu

lemma log_norm_eq (t u : ℂ) : Real.log ‖t - u‖ = posC t u - regC t 1 u := by
  unfold posC regC
  rw [div_eq_mul_inv, one_mul, Real.posLog_sub_posLog_inv]

lemma abs_log_norm_eq (t u : ℂ) : |Real.log ‖t - u‖| = posC t u + regC t 1 u := by
  unfold posC regC
  rw [div_eq_mul_inv, one_mul, Real.abs_log_eq_posLog_add_posLog_inv]

/-- `log ‖t - u‖` is `σ`-integrable for every `t`. -/
lemma integrable_log_norm_sub (hσ : BallMajA σ b A α) [IsFiniteMeasure σ] (t : ℂ) :
    Integrable (fun u => Real.log ‖t - u‖) σ := by
  have := (integrable_posC hσ t).sub (integrable_regC hσ one_pos t)
  exact this.congr (ae_of_all _ fun u => (log_norm_eq t u).symm)

/-- A uniform bound for the absolute logarithmic potential. -/
lemma integral_abs_log_le (hσ : BallMajA σ b A α) [IsFiniteMeasure σ] (t : ℂ) :
    ∫ u, |Real.log ‖t - u‖| ∂σ ≤ σ.real univ * Real.log (1 + ‖t‖ + b) + A / α := by
  simp_rw [abs_log_norm_eq]
  rw [integral_add (integrable_posC hσ t) (integrable_regC hσ one_pos t)]
  refine add_le_add ?_ ((integral_regC_le hσ one_pos t).trans (le_of_eq (by rw [Real.one_rpow, mul_one])))
  have := integral_mono_ae (μ := σ) (f := posC t) (g := fun _ => Real.log (1 + ‖t‖ + b))
    (integrable_posC hσ t) (integrable_const _) (posC_le hσ t)
  rw [integral_const, smul_eq_mul] at this
  exact this

/-! ### Potential and energy of `σ` -/

/-- `potC σ t = ∫ log ‖t - u‖ dσ(u)` (the paper's `-U^σ(t)`). -/
noncomputable def potC (σ : Measure ℂ) (t : ℂ) : ℝ := ∫ u, Real.log ‖t - u‖ ∂σ

/-- `energyC σ = ∬ log ‖u - v‖ dσ dσ` (the paper's `-I(σ)`). -/
noncomputable def energyC (σ : Measure ℂ) : ℝ := ∫ u, potC σ u ∂σ

/-- The configuration: `σ` (weight `-1`) and the circles about the points `t i`. -/
noncomputable def cfgZ (σ : Measure ℂ) {h : ℕ} (t : Fin h → ℂ) (ε : ℝ) :
    Option (Fin h) → Measure ℂ
  | none => σ
  | some i => circZ (t i) ε

instance cfgZ_finite (σ : Measure ℂ) [IsFiniteMeasure σ] {h : ℕ} (t : Fin h → ℂ) (ε : ℝ)
    (k : Option (Fin h)) : IsFiniteMeasure (cfgZ σ t ε k) := by
  cases k <;> simp only [cfgZ] <;> infer_instance

/-! ### Blocks (A), (B) -/

/-- Block (A): the self-energy of a circle. -/
lemma pair_circZ_self (c : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hint : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circZ c ε).prod (circZ c ε))) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circZ c ε).prod (circZ c ε)) = Real.log ε := by
  rw [integral_prod_symm _ hint]
  have : ∀ᵐ w ∂(circZ c ε), ∫ z, Real.log ‖z - w‖ ∂(circZ c ε) = Real.log ε := by
    filter_upwards [ae_dist_circZ c hε] with w hw
    rw [integral_log_circZ_max c hε w, hw, max_self]
  rw [integral_congr_ae this]
  simp

/-- Block (B): the mutual energy of two circles about distinct complex centres dominates
`log ‖c - c'‖`. -/
lemma pair_circZ_circZ_ge (c c' : ℂ) {ε : ℝ} (hε : 0 < ε) (hne : c ≠ c')
    (hint : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circZ c ε).prod (circZ c' ε))) :
    Real.log ‖c - c'‖ ≤
      ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circZ c ε).prod (circZ c' ε)) := by
  rw [integral_prod_symm _ hint]
  have h1 : Integrable (fun w : ℂ => ∫ z, Real.log ‖z - w‖ ∂(circZ c ε)) (circZ c' ε) :=
    hint.integral_prod_right
  have h2 : Integrable (fun w : ℂ => Real.log ‖c - w‖) (circZ c' ε) := by
    refine (integrable_log_circZ c' hε c).congr (ae_of_all _ fun w => ?_)
    simp only [norm_sub_rev]
  have h3 : ∀ᵐ w ∂(circZ c' ε), c ≠ w := by
    have := (measure_eq_zero_iff_ae_notMem.mp (circZ_singleton c' hε.ne' c))
    filter_upwards [this] with w hw hcw
    exact hw (by simp [hcw])
  have h4 : ∫ w, Real.log ‖c - w‖ ∂(circZ c' ε) = Real.log (max ε ‖c' - c‖) := by
    have e : ∀ w : ℂ, Real.log ‖c - w‖ = Real.log ‖w - c‖ := fun w => by
      rw [norm_sub_rev]
    simp_rw [e]
    exact integral_log_circZ_max c' hε c
  have h5 : Real.log ‖c - c'‖ ≤ Real.log (max ε ‖c' - c‖) := by
    have hpos : 0 < ‖c - c'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    refine Real.log_le_log hpos ?_
    rw [norm_sub_rev]
    exact le_max_right _ _
  calc Real.log ‖c - c'‖ ≤ Real.log (max ε ‖c' - c‖) := h5
    _ = ∫ w, Real.log ‖c - w‖ ∂(circZ c' ε) := h4.symm
    _ ≤ ∫ w, ∫ z, Real.log ‖z - w‖ ∂(circZ c ε) ∂(circZ c' ε) := by
        refine integral_mono_ae h2 h1 ?_
        filter_upwards [h3] with w hw
        rw [integral_log_circZ_max c hε w]
        exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hw)) (le_max_right _ _)

/-! ### Integrability and distinctness -/

section Hyp

variable [IsFiniteMeasure σ]

lemma integrable_circZ_circZ (c c' : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circZ c ε).prod (circZ c' ε)) := by
  refine integrable_log_prod (C := 2 * Real.log (1 + ‖c‖ + ε + (‖c'‖ + |ε|)) + |Real.log ε|) ?_ ?_
  · exact ae_of_all _ fun w => integrable_log_circZ c hε w
  · filter_upwards [ae_norm_circZ c' ε] with w hw
    exact integral_abs_log_circZ_le c hε w hw

lemma integrable_circZ_sigma (hσ : BallMajA σ b A α) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circZ c ε).prod σ) := by
  refine integrable_log_prod (C := 2 * Real.log (1 + ‖c‖ + ε + b) + |Real.log ε|) ?_ ?_
  · exact ae_of_all _ fun w => integrable_log_circZ c hε w
  · filter_upwards [hσ.ae_mem] with w hw
    exact integral_abs_log_circZ_le c hε w hw

lemma integrable_sigma_circZ (hσ : BallMajA σ b A α) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (σ.prod (circZ c ε)) :=
  integrable_log_swap (integrable_circZ_sigma hσ c hε)

lemma integrable_sigma_sigma (hσ : BallMajA σ b A α) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (σ.prod σ) := by
  refine integrable_log_prod
    (C := σ.real univ * Real.log (1 + b + b) + A / α) ?_ ?_
  · exact ae_of_all _ fun t => by
      refine (integrable_log_norm_sub hσ t).congr (ae_of_all _ fun u => ?_)
      simp only [norm_sub_rev]
  · filter_upwards [hσ.ae_mem] with t ht
    have e : ∀ u : ℂ, |Real.log ‖u - t‖| = |Real.log ‖t - u‖| := fun u => by rw [norm_sub_rev]
    simp_rw [e]
    refine (integral_abs_log_le hσ t).trans ?_
    have hmono : Real.log (1 + ‖t‖ + b) ≤ Real.log (1 + b + b) :=
      Real.log_le_log (by have := hσ.b_pos; positivity) (by linarith)
    have := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ σ.real univ)
    linarith

/-! ### Blocks (C), (D) -/

/-- Block (C), exact form: `∫ U dω_{c,ε} = potC σ c + ∫ log⁺(ε/‖c - u‖) dσ`. -/
lemma pair_circZ_sigma_eq (hσ : BallMajA σ b A α) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circZ c ε).prod σ) =
      potC σ c + ∫ u, regC c ε u ∂σ := by
  rw [integral_prod_symm _ (integrable_circZ_sigma hσ c hε)]
  have hae : ∀ᵐ u ∂σ, ∫ z, Real.log ‖z - u‖ ∂(circZ c ε) =
      Real.log ‖c - u‖ + regC c ε u := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hσ.singleton_zero c)] with u hu
    have : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hu (by simp [h])))
    rw [integral_log_circZ_max c hε u]
    exact log_max_eq_add hε this
  rw [integral_congr_ae hae, integral_add (integrable_log_norm_sub hσ c) (integrable_regC hσ hε c)]
  rfl

/-- Block (C): circle-to-`σ` energy is at most `potC σ c + A ε` (LD07). -/
lemma pair_circZ_sigma_le (hσ : BallMajA σ b A α) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circZ c ε).prod σ) ≤ potC σ c + A * ε ^ α / α := by
  rw [pair_circZ_sigma_eq hσ c hε]
  exact add_le_add le_rfl (integral_regC_le hσ hε c)

/-- Block (D): the energy of `σ`. -/
lemma pair_sigma_sigma (hσ : BallMajA σ b A α) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂(σ.prod σ) = energyC σ := by
  rw [integral_prod _ (integrable_sigma_sigma hσ)]
  rfl

end Hyp

/-! ### The configuration inequality at complex points -/

section Assembly

variable [IsFiniteMeasure σ] {h : ℕ}

/-- **The configuration inequality at complex points** (LD06 + LD07): for every `ε > 0` and
pairwise distinct `t_i ∈ ℂ` (`i < h`), with `h = K σ(ℂ)`,
`h log ε + ∑ᵢ ∑ᵢ' log ‖tᵢ - tᵢ'‖ ≤ 2K ∑ᵢ (potC σ tᵢ + A ε) - K² energyC σ`. -/
theorem energy_rawC (hσ : BallMajA σ b A α) {K : ℝ} (hK : 0 < K) (hh : (h : ℝ) = K * σ.real univ)
    (t : Fin h → ℂ) (ht : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    (h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log ‖t i - t i'‖ ≤
      2 * K * ∑ i, (potC σ (t i) + A * ε ^ α / α) - K ^ 2 * energyC σ := by
  set m : Option (Fin h) → Measure ℂ := cfgZ σ t ε with hm
  set s : Option (Fin h) → ℝ := fun o => o.elim (-1) (fun _ => 1 / K) with hs
  have hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ b + ε + ∑ i, ‖t i‖ := by
    intro k
    cases k with
    | none =>
      filter_upwards [hσ.ae_mem] with z hz
      have : 0 ≤ ∑ i, ‖t i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
      linarith
    | some i =>
      filter_upwards [ae_norm_circZ (t i) ε] with z hz
      have h1 : ‖t i‖ ≤ ∑ j, ‖t j‖ := Finset.single_le_sum (f := fun j => ‖t j‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      rw [abs_of_pos hε] at hz
      have := hσ.b_pos
      linarith
  have hmass : ∑ k, s k * (m k).real univ = 0 := by
    rw [Fintype.sum_option]
    simp only [hs, hm, cfgZ, Option.elim]
    simp only [probReal_univ, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [hh]; field_simp; ring
  have hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((m k).prod (m l)) := by
    intro k l
    cases k <;> cases l <;> simp only [hm, cfgZ]
    · exact integrable_sigma_sigma hσ
    · exact integrable_sigma_circZ hσ _ hε
    · exact integrable_circZ_sigma hσ _ hε
    · exact integrable_circZ_circZ _ _ hε
  have hae : ∀ k l, ∀ᵐ p ∂((m k).prod (m l)), p.1 ≠ p.2 := by
    intro k l
    cases l with
    | none => exact ae_ne_of_noAtoms_right hσ.singleton_zero
    | some j => exact ae_ne_of_noAtoms_right (circZ_singleton _ hε.ne')
  have hE := energy_log_nonpos hR hmass hint hae
  obtain ⟨L, hL⟩ : ∃ L : Fin h → Fin h → ℝ, ∀ i i',
      L i i' = pairInt m (fun z w => Real.log ‖z - w‖) (some i) (some i') :=
    ⟨fun i i' => pairInt m (fun z w => Real.log ‖z - w‖) (some i) (some i'), fun _ _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin h → ℝ, ∀ i,
      Q i = pairInt m (fun z w => Real.log ‖z - w‖) (some i) none :=
    ⟨fun i => pairInt m (fun z w => Real.log ‖z - w‖) (some i) none, fun _ => rfl⟩
  have hQle : ∀ i, Q i ≤ potC σ (t i) + A * ε ^ α / α := fun i => by
    rw [hQ]; exact pair_circZ_sigma_le hσ (t i) hε
  have hnn : pairInt m (fun z w => Real.log ‖z - w‖) none none = energyC σ :=
    pair_sigma_sigma hσ
  have hLii : ∀ i, L i i = Real.log ε := fun i => by
    rw [hL]; exact pair_circZ_self (t i) hε (integrable_circZ_circZ _ _ hε)
  have hLge : ∀ i i', i ≠ i' → Real.log ‖t i - t i'‖ ≤ L i i' := fun i i' hne => by
    rw [hL]
    exact pair_circZ_circZ_ge (t i) (t i') hε (fun e => hne (ht e)) (integrable_circZ_circZ _ _ hε)
  have hnS : ∀ i, pairInt m (fun z w => Real.log ‖z - w‖) none (some i) = Q i := fun i => by
    rw [hQ]; exact pairInt_swap m (some i) none
  unfold energy at hE
  rw [Fintype.sum_option] at hE
  simp only [Fintype.sum_option, hnn, hnS, ← hL, ← hQ] at hE
  simp only [hs, Option.elim] at hE
  rw [Finset.sum_add_distrib] at hE
  have e1 : ∑ i, (-1 : ℝ) * (1 / K) * Q i = -(1 / K) * ∑ i, Q i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (1 / K) * (-1 : ℝ) * Q i = -(1 / K) * ∑ i, Q i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, ∑ i', (1 / K) * (1 / K) * L i i' = (1 / K) ^ 2 * ∑ i, ∑ i', L i i' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  have hE' : energyC σ - 2 * (1 / K) * ∑ i, Q i + (1 / K) ^ 2 * ∑ i, ∑ i', L i i' ≤ 0 := by
    linarith [hE, e1, e2, e3]
  have hAB : (h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log ‖t i - t i'‖ ≤ ∑ i, ∑ i', L i i' := by
    have hi : ∀ i, Real.log ε + ∑ i', Real.log ‖t i - t i'‖ ≤ ∑ i', L i i' := by
      intro i
      rw [← Finset.add_sum_erase Finset.univ (fun i' => L i i') (Finset.mem_univ i), hLii i,
        ← Finset.sum_erase (s := Finset.univ) (a := i) (f := fun i' => Real.log ‖t i - t i'‖)
          (by simp)]
      refine add_le_add le_rfl (Finset.sum_le_sum fun i' hi' => ?_)
      exact hLge i i' (fun e => Finset.ne_of_mem_erase hi' e.symm)
    calc (h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log ‖t i - t i'‖
        = ∑ i : Fin h, (Real.log ε + ∑ i', Real.log ‖t i - t i'‖) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hi i
  have hQsum : ∑ i, Q i ≤ ∑ i, (potC σ (t i) + A * ε ^ α / α) :=
    Finset.sum_le_sum fun i _ => hQle i
  have hK2 : 0 < K ^ 2 := by positivity
  have h1 : K ^ 2 * (energyC σ - 2 * (1 / K) * ∑ i, Q i + (1 / K) ^ 2 * ∑ i, ∑ i', L i i') ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hK2.le hE'
  have h2 : K ^ 2 * (energyC σ - 2 * (1 / K) * ∑ i, Q i + (1 / K) ^ 2 * ∑ i, ∑ i', L i i') =
      K ^ 2 * energyC σ - 2 * K * ∑ i, Q i + ∑ i, ∑ i', L i i' := by
    field_simp
  have h3 : 2 * K * ∑ i, Q i ≤ 2 * K * ∑ i, (potC σ (t i) + A * ε ^ α / α) :=
    mul_le_mul_of_nonneg_left hQsum (by positivity)
  linarith [h1, h2, h3, hAB]

end Assembly


/-! ### Vandermonde determinants and the integral bound (LD09) -/

section Vandermonde

lemma sum_Ioi_card_mul_two (h : ℕ) : (∑ i : Fin h, (Finset.Ioi i).card) * 2 = h * (h - 1) := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i) h, Finset.sum_range_reflect (fun i => i) h,
    Finset.sum_range_id_mul_two]

lemma sum_Ioi_const (h : ℕ) (c : ℝ) :
    ∑ i : Fin h, ∑ _j ∈ Finset.Ioi i, c = (h : ℝ) * ((h : ℝ) - 1) / 2 * c := by
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
  have := sum_Ioi_card_mul_two h
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have hcast : ((∑ i : Fin h, (Finset.Ioi i).card : ℕ) : ℝ) = (h : ℝ) * ((h : ℝ) - 1) / 2 := by
    have h2 : (((∑ i : Fin h, (Finset.Ioi i).card) * 2 : ℕ) : ℝ) = ((h * (h - 1) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h)] at h2 ⊢
    linarith
  rw [← hcast]
  push_cast
  ring

/-- A symmetric kernel vanishing on the diagonal: the full double sum is twice the upper one. -/
lemma sum_sym_eq {h : ℕ} (f : Fin h → Fin h → ℝ) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  have h1 : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, not_lt.mpr hij.le]
    · simp [hd]
    · simp [hij, not_lt.mpr hij.le, hs i j]
  have e1 : ∑ i, ∑ j, (if i < j then f i j else 0) = ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  have e2 : ∑ i, ∑ j, (if j < i then f j i else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) :=
    Finset.sum_comm
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f j i else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if j < i then f j i else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by rw [e2, e1]; ring

/-- The logarithm of the squared Vandermonde modulus at `h` distinct points, in terms of the
rescaled points `v i / n`. -/
lemma log_vand_sq {h : ℕ} (v : Fin h → ℂ) (hinj : Function.Injective v) {n : ℝ} (hn : 0 < n) :
    Real.log (‖(Matrix.vandermonde v).det‖ ^ 2) =
      (h : ℝ) * ((h : ℝ) - 1) * Real.log n + ∑ i, ∑ j, Real.log ‖v i / n - v j / n‖ := by
  have hne : ∀ i j : Fin h, j ∈ Finset.Ioi i → v j - v i ≠ 0 := fun i j hj e =>
    (Finset.mem_Ioi.mp hj).ne' (hinj (sub_eq_zero.mp e))
  have hnorm : ∀ i j : Fin h, j ∈ Finset.Ioi i →
      ‖v j - v i‖ = n * ‖v j / n - v i / n‖ := by
    intro i j _
    rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    field_simp
  have hpos : ∀ i j : Fin h, j ∈ Finset.Ioi i → 0 < ‖v j / n - v i / n‖ := by
    intro i j hj
    refine norm_pos_iff.mpr fun e => ?_
    apply hne i j hj
    have : (v j - v i) / (n : ℂ) = 0 := by rw [sub_div]; exact e
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    exact (div_eq_zero_iff.mp this).resolve_right hn'
  rw [Matrix.det_vandermonde]
  simp only [norm_prod, ← Finset.prod_pow]
  rw [Real.log_prod (fun i _ => (Finset.prod_pos fun j hj =>
    pow_pos (norm_pos_iff.mpr (hne i j hj)) 2).ne')]
  have step : ∀ i : Fin h, Real.log (∏ j ∈ Finset.Ioi i, ‖v j - v i‖ ^ 2) =
      ∑ j ∈ Finset.Ioi i, (2 * Real.log n + 2 * Real.log ‖v j / n - v i / n‖) := by
    intro i
    rw [Real.log_prod (fun j hj => pow_ne_zero 2 (norm_pos_iff.mpr (hne i j hj)).ne')]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Real.log_pow, hnorm i j hj, Real.log_mul hn.ne' (hpos i j hj).ne']
    push_cast; ring
  simp_rw [step]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_Ioi_const]
  have hsym := sum_sym_eq (fun i j => Real.log ‖v i / n - v j / n‖)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have hfin : ∑ i, ∑ j, Real.log ‖v i / n - v j / n‖ =
      2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log ‖v j / n - v i / n‖ := by
    rw [hsym]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [norm_sub_rev]
  rw [hfin]
  ring

/-- The constant of the integral bound. -/
noncomputable def boundConst (σ : Measure ℂ) (A α n : ℝ) (h : ℕ) (ε : ℝ) : ℝ :=
  (h : ℝ) * ((h : ℝ) - 1) * Real.log n - (h : ℝ) * Real.log ε + 2 * n * h * (A * ε ^ α / α) -
    n ^ 2 * energyC σ

variable [IsFiniteMeasure σ]

/-- **Pointwise bound** (LD09, Step 4 of Theorem A): for `h = n σ(ℂ)` points `v i` in `ℂ`,
`‖Δ(v)‖² ≤ exp(B) ∏ᵢ exp(2n · potC σ (vᵢ/n))`. -/
theorem vand_sq_le (hσ : BallMajA σ b A α) {n : ℝ} (hn : 0 < n) {h : ℕ}
    (hh : (h : ℝ) = n * σ.real univ) {ε : ℝ} (hε : 0 < ε) (v : Fin h → ℂ) :
    ‖(Matrix.vandermonde v).det‖ ^ 2 ≤
      Real.exp (boundConst σ A α n h ε) * ∏ i, Real.exp (2 * n * potC σ (v i / n)) := by
  by_cases hinj : Function.Injective v
  · have hpos : 0 < ‖(Matrix.vandermonde v).det‖ ^ 2 := by
      have : (Matrix.vandermonde v).det ≠ 0 := by
        rw [Matrix.det_vandermonde_ne_zero_iff]; exact hinj
      positivity
    refine (Real.log_le_log_iff hpos (by positivity)).mp ?_
    rw [log_vand_sq v hinj hn, Real.log_mul (Real.exp_pos _).ne'
      (Finset.prod_pos fun i _ => Real.exp_pos _).ne', Real.log_exp,
      Real.log_prod (fun i _ => (Real.exp_pos _).ne')]
    simp only [Real.log_exp]
    have hs : Function.Injective fun i => v i / (n : ℂ) := by
      intro i j e
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      exact hinj ((div_left_inj' hn').mp e)
    have hE := energy_rawC hσ hn hh (fun i => v i / (n : ℂ)) hs hε
    simp only [boundConst]
    have hsum : ∑ i, (potC σ (v i / n) + A * ε ^ α / α) =
        ∑ i, potC σ (v i / n) + h * (A * ε ^ α / α) := by
      rw [Finset.sum_add_distrib]; simp
    rw [hsum] at hE
    have hmul : ∑ x, 2 * n * potC σ (v x / n) = 2 * n * ∑ x, potC σ (v x / n) :=
      (Finset.mul_sum _ _ _).symm
    rw [hmul]
    nlinarith [hE]
  · have : (Matrix.vandermonde v).det = 0 := by
      rw [Matrix.det_vandermonde_eq_zero_iff]
      by_contra hcon
      push Not at hcon
      exact hinj fun i j e => hcon i j e
    rw [this, norm_zero]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]; positivity

/-- **LD09, `complex_bound`**: for a σ-finite weight space `(X, m)`, a point map `z : X → ℂ`, a
nonnegative weight `g`, and the dual measure `σ` with `BallMajA`, `h = n σ(ℂ)` and `ε > 0`:
`∫_{X^h} ∏ g(xₗ) ‖Δ(z(x))‖² dm^h ≤ exp(B) (∫ g · exp(2n · potC σ (z/n)) dm)^h`. -/
theorem complex_bound {X : Type*} [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    (z : X → ℂ) (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hσ : BallMajA σ b A α) {n : ℝ} (hn : 0 < n)
    {h : ℕ} (hh : (h : ℝ) = n * σ.real univ) {ε : ℝ} (hε : 0 < ε)
    (hG : Integrable (fun x => g x * Real.exp (2 * n * potC σ (z x / n))) m) :
    ∫ x : Fin h → X, (∏ l, g (x l)) * ‖(Matrix.vandermonde fun l => z (x l)).det‖ ^ 2
        ∂(Measure.pi fun _ => m) ≤
      Real.exp (boundConst σ A α n h ε) *
        (∫ x, g x * Real.exp (2 * n * potC σ (z x / n)) ∂m) ^ h := by
  have hle : ∀ x : Fin h → X, (∏ l, g (x l)) * ‖(Matrix.vandermonde fun l => z (x l)).det‖ ^ 2 ≤
      Real.exp (boundConst σ A α n h ε) *
        ∏ l, (g (x l) * Real.exp (2 * n * potC σ (z (x l) / n))) := by
    intro x
    have h1 := vand_sq_le hσ hn hh hε (fun l => z (x l))
    have h2 : 0 ≤ ∏ l, g (x l) := Finset.prod_nonneg fun l _ => hg0 _
    calc (∏ l, g (x l)) * ‖(Matrix.vandermonde fun l => z (x l)).det‖ ^ 2
        ≤ (∏ l, g (x l)) * (Real.exp (boundConst σ A α n h ε) *
            ∏ l, Real.exp (2 * n * potC σ (z (x l) / n))) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by rw [Finset.prod_mul_distrib]; ring
  calc _ ≤ ∫ x : Fin h → X, Real.exp (boundConst σ A α n h ε) *
        ∏ l, (g (x l) * Real.exp (2 * n * potC σ (z (x l) / n))) ∂(Measure.pi fun _ => m) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
          ((Integrable.fintype_prod (f := fun _ (x : X) =>
            g x * Real.exp (2 * n * potC σ (z x / n))) fun _ => hG).const_mul _)
          (Filter.Eventually.of_forall hle)
        exact mul_nonneg (Finset.prod_nonneg fun l _ => hg0 _) (sq_nonneg _)
    _ = _ := by
        rw [integral_const_mul, integral_fintype_prod_eq_prod
          (f := fun _ (x : X) => g x * Real.exp (2 * n * potC σ (z x / n))),
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Vandermonde

end CatalanCore.Decay.ComplexEnergy
