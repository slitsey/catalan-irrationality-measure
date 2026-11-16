module

public import CatalanCore.Zeta5.Energy.Kernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/ZeroMass.lean and Apery/EnergyLimit.lean (Moritz Firsching); changes: module conversion, namespace CatalanCore.Zeta5.Energy; generalised from finitely many continuous curves on `[0, 2π]` to a finite family of finite measures on `ℂ` (the pair integral is an integral against the product measure, zero mass is `∑ s k * (m k).real univ = 0`). -/

/-!
# Lemma 6.2 (zero-mass logarithmic energy) for finite measures (ZD01)

A finite family of finite measures `m k` on `ℂ` with real weights `s k` and bounded support.
The pair integral of a kernel `f` is `pairInt m f k l = ∫ f z w d(m k ⊗ m l)` and
`energy s m f = ∑ k l, s k s l pairInt m f k l`.

* `energy_Ltr_nonpos` : for the truncated kernel `L_{a,b}` and zero weighted mass the energy is
  nonpositive (Gaussian positivity, `gaussian_energy_nonneg`);
* `energy_log_nonpos` : **ZD01**, the limit `a → 0, b → ∞` by dominated convergence, under the
  integrability of `log ‖z - w‖` on each `m k ⊗ m l` and a.e. distinctness `z ≠ w`.

A signed measure `ν = ν⁺ - ν⁻` of total mass `0` is the case `ι = Bool`, `s = (1, -1)`.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace CatalanCore.Zeta5.Energy

variable {ι : Type*}

/-- Double integral of a kernel against two measures. -/
noncomputable def pairInt (m : ι → Measure ℂ) (f : ℂ → ℂ → ℝ) (k l : ι) : ℝ :=
  ∫ p : ℂ × ℂ, f p.1 p.2 ∂((m k).prod (m l))

/-- The energy of the weighted family of measures. -/
noncomputable def energy [Fintype ι] (s : ι → ℝ) (m : ι → Measure ℂ) (f : ℂ → ℂ → ℝ) : ℝ :=
  ∑ k, ∑ l, s k * s l * pairInt m f k l

/-- Gaussian pair integral. -/
noncomputable def Gk (m : ι → Measure ℂ) (t : ℝ) (k l : ι) : ℝ :=
  ∫ p : ℂ × ℂ, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂((m k).prod (m l))

/-- Gaussian smoothing of one measure. -/
noncomputable def gk (m : ι → Measure ℂ) (t : ℝ) (k : ι) (u : ℂ) : ℝ :=
  ∫ z : ℂ, Real.exp (-(2 * t) * ‖z - u‖ ^ 2) ∂(m k)

lemma exp_neg_sq_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : Real.exp (-c * x ^ 2) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg x]

section Gaussian

variable {m : ι → Measure ℂ} [∀ k, IsFiniteMeasure (m k)]

lemma integrable_gauss_kernel {μ : Measure ℂ} [IsFiniteMeasure μ] {t : ℝ} (ht : 0 ≤ t) (u : ℂ) :
    Integrable (fun z : ℂ => Real.exp (-(2 * t) * ‖z - u‖ ^ 2)) μ :=
  Integrable.mono' (integrable_const (1 : ℝ))
    (by exact (by fun_prop : Continuous fun z : ℂ =>
      Real.exp (-(2 * t) * ‖z - u‖ ^ 2)).aestronglyMeasurable)
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_neg_sq_le_one (by linarith) _)

lemma gk_nonneg (t : ℝ) (k : ι) (u : ℂ) : 0 ≤ gk m t k u :=
  integral_nonneg fun _ => (Real.exp_pos _).le

lemma continuous_gk {t : ℝ} (ht : 0 ≤ t) (k : ι) : Continuous (gk m t k) := by
  unfold gk
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun u => ?_) (fun u => ?_)
    (integrable_const _) (ae_of_all _ fun z => ?_)
  · exact (by fun_prop : Continuous fun z : ℂ =>
      Real.exp (-(2 * t) * ‖z - u‖ ^ 2)).aestronglyMeasurable
  · exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_neg_sq_le_one (by linarith) _
  · fun_prop

lemma gk_le_mass {t : ℝ} (ht : 0 ≤ t) (k : ι) (u : ℂ) : gk m t k u ≤ (m k).real univ := by
  unfold gk
  have := integral_mono (μ := m k)
    (f := fun z : ℂ => Real.exp (-(2 * t) * ‖z - u‖ ^ 2)) (g := fun _ => (1 : ℝ))
    (integrable_gauss_kernel ht u)
    (integrable_const _) (fun z => exp_neg_sq_le_one (by linarith) _)
  simpa [Measure.real] using this

lemma gk_le {R : ℝ} (hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ R) {t : ℝ} (ht : 0 ≤ t) (k : ι) (u : ℂ) :
    gk m t k u ≤ (m k).real univ * Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2) := by
  unfold gk
  have := integral_mono_ae (μ := m k)
    (f := fun z : ℂ => Real.exp (-(2 * t) * ‖z - u‖ ^ 2))
    (g := fun _ => Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2))
    (integrable_gauss_kernel ht u) (integrable_const _)
    (by filter_upwards [hR k] with z hz using exp_gauss_le ht hz)
  rw [MeasureTheory.integral_const, smul_eq_mul] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The Gaussian pair integral as an integral over `ℂ` of a product of smoothed measures. -/
lemma Gk_eq {R : ℝ} (hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (k l : ι) :
    Gk m t k l = 4 * t / π * ∫ u : ℂ, gk m t k u * gk m t l u := by
  have hconv : ∀ z w : ℂ, Real.exp (-t * ‖z - w‖ ^ 2) =
      4 * t / π * ∫ u : ℂ, Real.exp (-(2 * t) * ‖z - u‖ ^ 2) * Real.exp (-(2 * t) * ‖w - u‖ ^ 2) := by
    intro z w
    rw [gaussian_conv ht]
    field_simp
  unfold Gk
  simp_rw [hconv]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hint : Integrable (Function.uncurry fun (p : ℂ × ℂ) (u : ℂ) =>
      Real.exp (-(2 * t) * ‖p.1 - u‖ ^ 2) * Real.exp (-(2 * t) * ‖p.2 - u‖ ^ 2))
      (((m k).prod (m l)).prod volume) := by
    have hg : Integrable (fun q : (ℂ × ℂ) × ℂ => Real.exp (2 * t * R ^ 2) *
        Real.exp (-t * ‖(0 : ℂ) - q.2‖ ^ 2)) (((m k).prod (m l)).prod volume) :=
      (integrable_const (Real.exp (2 * t * R ^ 2))).mul_prod (integrable_gaussC ht 0)
    refine hg.mono' ?_ ?_
    · exact (by fun_prop : Continuous fun q : (ℂ × ℂ) × ℂ =>
        Real.exp (-(2 * t) * ‖q.1.1 - q.2‖ ^ 2) *
          Real.exp (-(2 * t) * ‖q.1.2 - q.2‖ ^ 2)).aestronglyMeasurable
    · have h1 : ∀ᵐ p ∂((m k).prod (m l)), ‖p.1‖ ≤ R :=
        Measure.quasiMeasurePreserving_fst.ae (hR k)
      have h2 : ∀ᵐ q ∂(((m k).prod (m l)).prod (volume : Measure ℂ)), ‖q.1.1‖ ≤ R :=
        Measure.quasiMeasurePreserving_fst.ae h1
      filter_upwards [h2] with q hq
      simp only [Function.uncurry, zero_sub, norm_neg, Real.norm_eq_abs]
      rw [abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
      calc Real.exp (-(2 * t) * ‖q.1.1 - q.2‖ ^ 2) * Real.exp (-(2 * t) * ‖q.1.2 - q.2‖ ^ 2)
          ≤ (Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖q.2‖ ^ 2)) * 1 :=
            mul_le_mul (exp_gauss_le ht.le hq) (exp_neg_sq_le_one (by linarith) _)
              (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  exact integral_prod_mul (fun z : ℂ => Real.exp (-(2 * t) * ‖z - u‖ ^ 2))
    (fun w : ℂ => Real.exp (-(2 * t) * ‖w - u‖ ^ 2))

/-- The Gaussian energy is nonnegative. -/
lemma gaussian_energy_nonneg [Fintype ι] {s : ι → ℝ} {R : ℝ} (hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ R)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑ k, ∑ l, s k * s l * Gk m t k l := by
  simp_rw [Gk_eq hR ht]
  have hint : ∀ k l : ι, Integrable (fun u : ℂ => gk m t k u * gk m t l u) := by
    intro k l
    have hg : Integrable (fun u : ℂ => ((m k).real univ * Real.exp (2 * t * R ^ 2) * (m l).real univ) *
        Real.exp (-t * ‖(0 : ℂ) - u‖ ^ 2)) := (integrable_gaussC ht 0).const_mul _
    refine hg.mono' ((continuous_gk ht.le k).mul (continuous_gk ht.le l)).aestronglyMeasurable ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gk_nonneg _ _ _) (gk_nonneg _ _ _))]
    simp only [zero_sub, norm_neg]
    calc gk m t k u * gk m t l u
        ≤ ((m k).real univ * Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2)) * (m l).real univ :=
          mul_le_mul (gk_le hR ht.le k u) (gk_le_mass ht.le l u) (gk_nonneg _ _ _)
            (by positivity)
      _ = _ := by ring
  have e : ∑ k, ∑ l, s k * s l * (4 * t / π * ∫ u : ℂ, gk m t k u * gk m t l u) =
      4 * t / π * ∫ u : ℂ, (∑ k, s k * gk m t k u) ^ 2 := by
    have : ∀ u : ℂ, (∑ k, s k * gk m t k u) ^ 2 =
        ∑ k, ∑ l, s k * s l * (gk m t k u * gk m t l u) := by
      intro u
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => (hint k l).const_mul _))]
    simp_rw [integral_finsetSum _ (fun l _ => (hint _ l).const_mul _),
      MeasureTheory.integral_const_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

end Gaussian

/-! ### The truncated kernel -/

section Truncated

variable {m : ι → Measure ℂ} [∀ k, IsFiniteMeasure (m k)]

lemma prod_real_univ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ.prod ν).real univ = μ.real univ * ν.real univ := by
  simp only [Measure.real]
  rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

/-- Continuity of the Gaussian pair integral in the parameter, for `t ≥ 0`. -/
lemma continuousOn_Gk (k l : ι) : ContinuousOn (fun t => Gk m t k l) (Ici 0) := by
  unfold Gk
  refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) (fun t ht => ?_) (fun t ht => ?_)
    (integrable_const _) (ae_of_all _ fun p => ?_)
  · exact (by fun_prop : Continuous fun p : ℂ × ℂ =>
      Real.exp (-t * ‖p.1 - p.2‖ ^ 2)).aestronglyMeasurable
  · exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_neg_sq_le_one (by simpa using ht) _
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)).continuousOn

lemma integrable_gauss_pair (k l : ι) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun p : ℂ × ℂ => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) ((m k).prod (m l)) :=
  Integrable.mono' (integrable_const (1 : ℝ))
    (by exact (by fun_prop : Continuous fun p : ℂ × ℂ =>
      Real.exp (-t * ‖p.1 - p.2‖ ^ 2)).aestronglyMeasurable)
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_neg_sq_le_one ht _)

/-- The truncated-kernel pair integral in terms of Gaussian pair integrals. -/
lemma pairInt_Ltr {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k l : ι) :
    pairInt m (fun z w => Ltr a b ‖z - w‖) k l =
      (1 / 2) * ∫ s in a..b,
        (Real.exp (-s) * ((m k).real univ * (m l).real univ) - Gk m s k l) / s := by
  unfold pairInt
  simp_rw [Ltr_eq_max ha hab]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hinv := continuous_inv_max ha
  have hcont : Continuous (Function.uncurry fun (p : ℂ × ℂ) (s : ℝ) =>
      (Real.exp (-s) - Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) * (max s a)⁻¹) := by
    have h1 : Continuous fun q : (ℂ × ℂ) × ℝ =>
        Real.exp (-q.2) - Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2) := by fun_prop
    exact h1.mul (hinv.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (p : ℂ × ℂ) (s : ℝ) =>
      (Real.exp (-s) - Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) * (max s a)⁻¹)
      (((m k).prod (m l)).prod (volume.restrict (Ioc a b))) := by
    refine Integrable.mono' (integrable_const (a⁻¹)) hcont.aestronglyMeasurable ?_
    have h2 : ∀ᵐ q ∂(((m k).prod (m l)).prod (volume.restrict (Ioc a b))), q.2 ∈ Ioc a b :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [h2] with q hq
    have hs : 0 < q.2 := ha.trans hq.1
    have e1 : 0 < Real.exp (-q.2) := Real.exp_pos _
    have e2 : 0 < Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2) := Real.exp_pos _
    have e3 : Real.exp (-q.2) ≤ 1 := by simpa using exp_neg_sq_le_one hs.le 1
    have e4 : Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2) ≤ 1 := exp_neg_sq_le_one hs.le _
    have hd : |Real.exp (-q.2) - Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hm : (max q.2 a)⁻¹ ≤ a⁻¹ := inv_anti₀ ha (le_max_right _ _)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos (inv_pos.mpr (lt_max_of_lt_right ha))]
    calc _ ≤ 1 * a⁻¹ := mul_le_mul hd hm (by positivity) zero_le_one
      _ = a⁻¹ := one_mul _
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 < s := ha.trans hs.1
  rw [max_eq_left hs.1.le, MeasureTheory.integral_mul_const,
    MeasureTheory.integral_sub (integrable_const _) (integrable_gauss_pair k l hs0.le), MeasureTheory.integral_const,
    prod_real_univ, smul_eq_mul, div_eq_mul_inv]
  unfold Gk
  ring

/-- **Lemma 6.2 for the truncated kernel**: the energy of a zero-mass combination of measures
with respect to `L_{a,b}` is nonpositive. -/
theorem energy_Ltr_nonpos [Fintype ι] {s : ι → ℝ} {R : ℝ} (hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ R)
    (hmass : ∑ k, s k * (m k).real univ = 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    energy s m (fun z w => Ltr a b ‖z - w‖) ≤ 0 := by
  unfold energy
  simp_rw [pairInt_Ltr ha hab]
  have hc : ∀ k l : ι, ContinuousOn
      (fun t => (Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t)
      (uIcc a b) := by
    intro k l
    rw [uIcc_of_le hab]
    apply ContinuousOn.div
    · exact (((by fun_prop : Continuous fun t : ℝ =>
        Real.exp (-t) * ((m k).real univ * (m l).real univ)).continuousOn).sub
        ((continuousOn_Gk k l).mono fun t ht => (ha.trans_le ht.1).le))
    · exact continuousOn_id
    · intro t ht; exact (ha.trans_le ht.1).ne'
  have e : ∑ k, ∑ l, s k * s l * ((1 / 2) * ∫ t in a..b,
      (Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t) =
      (1 / 2) * ∫ t in a..b, ∑ k, ∑ l, s k * s l *
        ((Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t) := by
    rw [intervalIntegral.integral_finsetSum
      (f := fun k t => ∑ l, s k * s l *
        ((Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t))
      (fun k _ => (continuousOn_finsetSum _ fun l _ =>
        continuousOn_const.mul (hc k l)).intervalIntegrable), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_finsetSum
      (f := fun l t => s k * s l *
        ((Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t))
      (fun l _ => (continuousOn_const.mul (hc k l)).intervalIntegrable), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_const_mul]; ring
  rw [e]
  have hpt : ∀ t ∈ Icc a b, 0 ≤ -(∑ k, ∑ l, s k * s l *
      ((Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hJ := gaussian_energy_nonneg (s := s) hR ht0
    have hA : ∑ k, ∑ l, s k * s l * (Real.exp (-t) * ((m k).real univ * (m l).real univ)) = 0 := by
      have : ∑ k, ∑ l, s k * s l * (Real.exp (-t) * ((m k).real univ * (m l).real univ)) =
          Real.exp (-t) * (∑ k, s k * (m k).real univ) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
      rw [this, hmass]; ring
    have : ∑ k, ∑ l, s k * s l *
        ((Real.exp (-t) * ((m k).real univ * (m l).real univ) - Gk m t k l) / t) =
        (∑ k, ∑ l, s k * s l * (Real.exp (-t) * ((m k).real univ * (m l).real univ)) -
          ∑ k, ∑ l, s k * s l * Gk m t k l) / t := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, hA, zero_sub, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hJ) ht0.le
  have := intervalIntegral.integral_nonneg (μ := volume) hab hpt
  rw [intervalIntegral.integral_neg] at this
  linarith

end Truncated

/-! ### The logarithmic kernel -/

section Limit

variable {m : ι → Measure ℂ} [∀ k, IsFiniteMeasure (m k)]

/-- Limit of the truncated pair integrals. -/
lemma tendsto_pairInt_Ltr (k l : ι)
    (hint : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((m k).prod (m l)))
    (hae : ∀ᵐ p ∂((m k).prod (m l)), p.1 ≠ p.2) :
    Tendsto (fun n : ℕ => pairInt m (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖) k l)
      atTop (𝓝 (pairInt m (fun z w => Real.log ‖z - w‖) k l)) := by
  have hn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hn' : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := fun n => by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcont : ∀ n : ℕ, Continuous fun p : ℂ × ℂ =>
      Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖p.1 - p.2‖ := fun n =>
    (continuous_Ltr (hn n) (hn' n)).comp (by fun_prop)
  unfold pairInt
  refine tendsto_integral_of_dominated_convergence
    (fun p => |Real.log ‖p.1 - p.2‖|) (fun n => (hcont n).aestronglyMeasurable)
    hint.abs ?_ ?_
  · intro n
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact abs_Ltr_le (hn n) (hn' n) (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  · filter_upwards [hae] with p hp
    exact tendsto_Ltr (norm_pos_iff.mpr (sub_ne_zero.mpr hp))

/-- **ZD01, Lemma 6.2** (zero-mass logarithmic energy) for a finite family of finite measures of
bounded support: if `∑ s k * m k(ℂ) = 0`, `log ‖z - w‖` is integrable on each `m k ⊗ m l` and
`z ≠ w` almost everywhere there, then `∑ k l, s k s l ∬ log ‖z - w‖ d m k d m l ≤ 0`. -/
theorem energy_log_nonpos [Fintype ι] {s : ι → ℝ} {R : ℝ} (hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ R)
    (hmass : ∑ k, s k * (m k).real univ = 0)
    (hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((m k).prod (m l)))
    (hae : ∀ k l, ∀ᵐ p ∂((m k).prod (m l)), p.1 ≠ p.2) :
    energy s m (fun z w => Real.log ‖z - w‖) ≤ 0 := by
  have hn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hn' : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := fun n => by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hle : ∀ n : ℕ, energy s m (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖) ≤ 0 :=
    fun n => energy_Ltr_nonpos hR hmass (hn n) (hn' n)
  have hlim : Tendsto
      (fun n : ℕ => energy s m (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖))
      atTop (𝓝 (energy s m (fun z w => Real.log ‖z - w‖))) := by
    unfold energy
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
    exact (tendsto_pairInt_Ltr k l (hint k l) (hae k l)).const_mul _
  exact le_of_tendsto' hlim hle

/-- ZD01 for two finite measures of equal mass (the zero-mass signed measure `μ₁ - μ₂`):
`I(μ₁) - I(μ₁, μ₂) - I(μ₂, μ₁) + I(μ₂) ≤ 0`. -/
theorem energy_log_nonpos_two {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {R : ℝ}
    (h₁ : ∀ᵐ z ∂μ₁, ‖z‖ ≤ R) (h₂ : ∀ᵐ z ∂μ₂, ‖z‖ ≤ R) (hmass : μ₁.real univ = μ₂.real univ)
    (hint₁₁ : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ₁.prod μ₁))
    (hint₁₂ : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ₁.prod μ₂))
    (hint₂₁ : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ₂.prod μ₁))
    (hint₂₂ : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ₂.prod μ₂))
    (hae₁₁ : ∀ᵐ p ∂(μ₁.prod μ₁), p.1 ≠ p.2) (hae₁₂ : ∀ᵐ p ∂(μ₁.prod μ₂), p.1 ≠ p.2)
    (hae₂₁ : ∀ᵐ p ∂(μ₂.prod μ₁), p.1 ≠ p.2) (hae₂₂ : ∀ᵐ p ∂(μ₂.prod μ₂), p.1 ≠ p.2) :
    (∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂(μ₁.prod μ₁)) -
      (∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂(μ₁.prod μ₂)) -
      (∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂(μ₂.prod μ₁)) +
      (∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂(μ₂.prod μ₂)) ≤ 0 := by
  let m : Bool → Measure ℂ := fun b => bif b then μ₁ else μ₂
  haveI : ∀ k, IsFiniteMeasure (m k) := fun k => by
    cases k
    · exact (inferInstance : IsFiniteMeasure μ₂)
    · exact (inferInstance : IsFiniteMeasure μ₁)
  have key := energy_log_nonpos (ι := Bool) (m := m) (s := fun b => bif b then 1 else -1) (R := R)
    (fun k => by cases k <;> simp only [m] <;> assumption)
    (by simp [Fintype.sum_bool, m, hmass])
    (fun k l => by cases k <;> cases l <;> simp only [m] <;> assumption)
    (fun k l => by cases k <;> cases l <;> simp only [m] <;> assumption)
  simp only [energy, pairInt, Fintype.sum_bool, m, cond_true, cond_false] at key
  linarith

end Limit

end CatalanCore.Zeta5.Energy
