module

public import CatalanCore.Tools.Joukowski
public import CatalanCore.Decay.ComplexEnergy
public import CatalanCore.Decay.WedgeBounds

@[expose] public section

/-!
# The wedge energy: closed-form self energy and the cross energy over the A-cell partition
(Lai decay, LD14, Lemma W4)

Generic in the segment `{M + h x : |x| ≤ 1}` (`M, h ∈ ℂ`, `h ≠ 0`) and the Chebyshev density
`f = Σ_{k ≤ N} c_k T_k ≥ 0`; no Lai numbers.  Sign convention of `ComplexEnergy`:
`potC σ t = ∫ log ‖t - u‖ dσ` and `energyC σ = ∬ log ‖u - v‖ dσ dσ`, so the paper's `I(σ)` is
`-energyC σ` and `U^σ = logPotC σ = -potC σ`.

* `potC_seg_inside`: the potential of `f ω` at a point of its own segment.
* `energyC_segMeasure` (**W4(i), self energy**): `E(ν) = c₀² (log|h| - log 2) - Σ c_k²/(2k)`,
  that is `I(s₊) = -c₀² log(|h|/2) + Σ c_k²/(2k)`.
* `energyC_add_seg`: bilinearity for two segment measures whose segments miss each other
  (integrability from the closed form `logPotC_segMeasure` and `integral_chebF_log_inside`).
* `energy_conj_pair` (**W4(i)**): for `σ = s₊ + s̄₊`,
  `I(σ) = 2 I(s₊) + 2 I(s₊, s₋)`, `I(s₊, s₋) = (1/π) ∫₀^π f(cos φ) g(φ) dφ`,
  `g φ = U^{s₋}(M + h cos φ)`.
* `Ftow`, `Vf`, `cosCurve`, `isTower_cross`, `cross_U5_le`: the order-5 towers of `f(cos ·)` and of
  `g` along the angle, with the harmonic remainder of W3.
* `cross_cell_le`, `cross_partition_le` (**W4(ii)**): the Taylor integral with Leibniz remainder
  over one cell, and over an exact partition.
* `energy_conj_pair_le`: `I(σ) ≤ 2 I(s₊) + (2/π) Σ_cells [2(b₀ r + b₂ r³/3 + b₄ r⁵/5) + E r⁶/3]`.
-/

namespace CatalanCore.Lai.DecayEnergy

open Polynomial Complex Set MeasureTheory Filter Topology CatalanCore.Tools.Joukowski
  CatalanCore.Zeta5.Potential CatalanCore.Decay.ComplexEnergy
  CatalanMeasure.GenD.Signed.TaylorCell CatalanCore.Decay.WedgeBounds CatalanCore.Zeta5.Cells

noncomputable section

theorem measurable_potC (σ : Measure ℂ) [SFinite σ] : Measurable (potC σ) := by
  unfold potC
  have h : Measurable fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖ := by fun_prop
  exact (h.stronglyMeasurable.integral_prod_right').measurable

theorem integrable_segMeasure_iff {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {g : ℂ → ℝ} (hg : Measurable g) :
    Integrable g (segMeasure M h c N) ↔
      Integrable (fun θ => chebF c N (Real.cos θ) * g (M + h * (Real.cos θ : ℂ))) arc := by
  unfold segMeasure
  rw [integrable_map_measure hg.aestronglyMeasurable (continuous_segMap M h).measurable.aemeasurable]
  refine (integrable_withDensity_iff_integrable_smul'
      (f := fun θ => ENNReal.ofReal (chebF c N (Real.cos θ)))
      (ENNReal.measurable_ofReal.comp (continuous_chebF_cos c N).measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).trans ?_
  have : ∀ θ : ℝ, (ENNReal.ofReal (chebF c N (Real.cos θ))).toReal • (g ∘ fun θ : ℝ =>
      M + h * (Real.cos θ : ℂ)) θ = chebF c N (Real.cos θ) * g (M + h * (Real.cos θ : ℂ)) := by
    intro θ
    simp only [smul_eq_mul, Function.comp]
    rw [ENNReal.toReal_ofReal (hpos _ (cos_mem θ))]
  simp_rw [this]

theorem norm_seg_sub {M h : ℂ} (x y : ℝ) :
    ‖(M + h * (x : ℂ)) - (M + h * (y : ℂ))‖ = ‖h‖ * |x - y| := by
  have : (M + h * (x : ℂ)) - (M + h * (y : ℂ)) = h * ((x - y : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The potential of the segment measure at a point of the segment, with integrability. -/
theorem potC_seg_inside {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun u => Real.log ‖(M + h * (x : ℂ)) - u‖) (segMeasure M h c N) ∧
    potC (segMeasure M h c N) (M + h * (x : ℂ)) =
      c 0 * Real.log ‖h‖ - Real.log 2 * c 0 - ∑ k ∈ Finset.range N,
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  have hmeas : Measurable fun u : ℂ => Real.log ‖(M + h * (x : ℂ)) - u‖ :=
    Real.measurable_log.comp (by fun_prop)
  obtain ⟨hint, hval⟩ := integral_chebF_log_inside c N hx
  have hhn : ‖h‖ ≠ 0 := norm_ne_zero_iff.2 hh
  have hae : ∀ᵐ θ ∂arc, chebF c N (Real.cos θ) * Real.log ‖(M + h * (x : ℂ)) -
      (M + h * (Real.cos θ : ℂ))‖ =
      Real.log ‖h‖ * chebF c N (Real.cos θ) +
        chebF c N (Real.cos θ) * Real.log |x - Real.cos θ| := by
    filter_upwards [ae_cos_ne x hx] with θ hθ
    rw [norm_seg_sub, Real.log_mul hhn (abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hθ)))]
    ring
  have hint2 : Integrable (fun θ => chebF c N (Real.cos θ) * Real.log ‖(M + h * (x : ℂ)) -
      (M + h * (Real.cos θ : ℂ))‖) arc :=
    ((integrable_chebF c N).const_mul _).add hint |>.congr (hae.mono fun θ hθ => hθ.symm)
  refine ⟨(integrable_segMeasure_iff hpos hmeas).2 hint2, ?_⟩
  unfold potC
  rw [integral_segMeasure hpos hmeas, integral_congr_ae hae,
    integral_add ((integrable_chebF c N).const_mul _) hint, integral_const_mul, integral_chebF, hval]
  ring


/-! ### Finiteness, the self energy, and integrability on a segment -/

theorem isFiniteMeasure_seg {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) : IsFiniteMeasure (segMeasure M h c N) := by
  unfold segMeasure
  haveI : IsFiniteMeasure (arc.withDensity fun θ => ENNReal.ofReal (chebF c N (Real.cos θ))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_chebF c N).2
  infer_instance

theorem potC_eq_neg_logPotC (ν : Measure ℂ) (s : ℂ) : potC ν s = - logPotC ν s := by
  unfold potC logPotC; ring

/-- **W4(i), the self energy (LD14).**  `∬ log |u - v| dν dν = c₀² (log |h| - log 2)
- Σ_{k ≥ 1} c_k² / (2k)` for `ν = f ω` on the segment `{M + h x}`; in the paper's sign,
`I(ν) = -c₀² log(|h|/2) + Σ c_k²/(2k)`. -/
theorem energyC_segMeasure {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) :
    energyC (segMeasure M h c N) = c 0 ^ 2 * (Real.log ‖h‖ - Real.log 2) -
      ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) := by
  haveI := isFiniteMeasure_seg (M := M) (h := h) hpos
  unfold energyC
  rw [integral_segMeasure hpos (measurable_potC _)]
  have e1 : ∀ θ : ℝ, chebF c N (Real.cos θ) * potC (segMeasure M h c N) (M + h * (Real.cos θ : ℂ)) =
      (c 0 * Real.log ‖h‖ - Real.log 2 * c 0) * chebF c N (Real.cos θ) - ∑ k ∈ Finset.range N,
        (c (k + 1) / ((k + 1 : ℕ) : ℝ)) * (chebF c N (Real.cos θ) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) := by
    intro θ
    rw [(potC_seg_inside hh hpos (cos_mem θ)).2, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e1]
  rw [integral_sub ((integrable_chebF c N).const_mul _)
    (integrable_finsetSum _ fun k _ => (integrable_chebF_T c N _).const_mul _),
    integral_const_mul, integral_chebF, integral_finsetSum _ fun k _ =>
      (integrable_chebF_T c N _).const_mul _]
  have e2 : ∀ k ∈ Finset.range N, ∫ θ, (c (k + 1) / ((k + 1 : ℕ) : ℝ)) * (chebF c N (Real.cos θ) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) ∂arc =
      c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    rw [integral_const_mul, integral_chebF_mul_T]
    have hk' : k + 1 ≤ N := by simp at hk; omega
    simp only [hk', ite_true, Nat.succ_ne_zero, ite_false]
    field_simp
  rw [Finset.sum_congr rfl e2]
  ring

/-- A measurable function continuous along the segment is `ν`-integrable. -/
theorem integrable_seg_of_continuousOn {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {g : ℂ → ℝ} (hg : Measurable g)
    (hc : ContinuousOn (fun x : ℝ => g (M + h * (x : ℂ))) (Icc (-1 : ℝ) 1)) :
    Integrable g (segMeasure M h c N) := by
  refine (integrable_segMeasure_iff hpos hg).2 ?_
  have hc' : ContinuousOn (fun x : ℝ => chebF c N x * g (M + h * (x : ℂ))) (Icc (-1 : ℝ) 1) :=
    (continuous_chebF c N).continuousOn.mul hc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
  refine Integrable.mono' (integrable_const C)
    (((continuous_chebF_cos c N).measurable.mul
      (hg.comp (continuous_segMap M h).measurable)).aestronglyMeasurable)
    (ae_of_all _ fun θ => ?_)
  simpa using hC _ (cos_mem θ)

theorem norm_seg_sub_ne {M h : ℂ} (hh : h ≠ 0) {t : ℂ} (ht : 1 < jc ((t - M) / h))
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : ‖t - (M + h * (x : ℂ))‖ ≠ 0 := by
  have h1 := norm_sub_seg_ge (M := M) (s := t) hh hx
  have h2 : 0 < ‖h‖ * (jc ((t - M) / h) - 1) := mul_pos (norm_pos_iff.2 hh) (by linarith)
  exact (lt_of_lt_of_le h2 h1).ne'

/-- `u ↦ log |t - u|` is `ν`-integrable for `t` off the segment. -/
theorem integrable_log_seg_off {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {t : ℂ} (ht : 1 < jc ((t - M) / h)) :
    Integrable (fun u => Real.log ‖t - u‖) (segMeasure M h c N) :=
  integrable_seg_of_continuousOn hpos (Real.measurable_log.comp (by fun_prop))
    (ContinuousOn.log (by fun_prop) fun x hx => norm_seg_sub_ne hh ht hx)

theorem continuousAt_logPotC_seg {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    ContinuousAt (logPotC (segMeasure M h c N)) s := by
  have hζc : Continuous fun z : ℂ => (z - M) / h := (continuous_id.sub continuous_const).div_const h
  have hopen : {z : ℂ | 1 < jc ((z - M) / h)} ∈ 𝓝 s :=
    (isOpen_jc.preimage hζc).mem_nhds hs
  have hζ : ContinuousAt (fun z : ℂ => (z - M) / h) s := hζc.continuousAt
  have hR : ContinuousAt (fun z : ℂ => jR ((z - M) / h)) s :=
    ContinuousAt.comp (g := jR) (f := fun z : ℂ => (z - M) / h) (x := s) continuous_jR.continuousAt hζ
  have hP : ContinuousAt (fun z : ℂ => jphi ((z - M) / h)) s :=
    ContinuousAt.comp (g := jphi) (f := fun z : ℂ => (z - M) / h) (x := s) (continuousAt_jphi hs) hζ
  have hF : ContinuousAt (fun z : ℂ => -c 0 * Real.log ‖h‖ - c 0 * Real.log (jR ((z - M) / h) / 2) +
      ∑ k ∈ Finset.range N, c (k + 1) * ((jphi ((z - M) / h) ^ (k + 1))⁻¹).re /
        ((k + 1 : ℕ) : ℝ)) s := by
    have hlog : ContinuousAt (fun z : ℂ => Real.log (jR ((z - M) / h) / 2)) s := by
      refine ContinuousAt.log (hR.div_const 2) ?_
      have := one_lt_jR hs
      linarith
    have hsum : ContinuousAt (fun z : ℂ => ∑ k ∈ Finset.range N, c (k + 1) *
        ((jphi ((z - M) / h) ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ)) s := by
      refine tendsto_finsetSum _ fun k _ => ?_
      refine ContinuousAt.div_const (ContinuousAt.mul continuousAt_const ?_) _
      have h1 : ContinuousAt (fun z : ℂ => (jphi ((z - M) / h) ^ (k + 1))⁻¹) s :=
        (hP.pow (k + 1)).inv₀ (pow_ne_zero _ (jphi_ne_zero hs))
      exact ContinuousAt.comp (g := Complex.re) (f := fun z : ℂ => (jphi ((z - M) / h) ^ (k + 1))⁻¹)
        (x := s) Complex.continuous_re.continuousAt h1
    exact (continuousAt_const.sub (continuousAt_const.mul hlog)).add hsum
  refine hF.congr (Filter.eventuallyEq_of_mem hopen fun z hz => ?_)
  exact (logPotC_segMeasure hh hpos hz).symm

/-- The potential of `ν'` is `ν`-integrable when `ν`'s segment is off `ν'`'s. -/
theorem integrable_potC_cross {M h M' h' : ℂ} (hh' : h' ≠ 0) {c c' : ℕ → ℝ} {N N' : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hpos' : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c' N' x)
    (hsep : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M + h * (x : ℂ) - M') / h')) :
    Integrable (potC (segMeasure M' h' c' N')) (segMeasure M h c N) := by
  haveI := isFiniteMeasure_seg (M := M') (h := h') hpos'
  refine integrable_seg_of_continuousOn hpos (measurable_potC _) ?_
  intro x hx
  have hc : ContinuousAt (fun y : ℝ => M + h * (y : ℂ)) x := by fun_prop
  have h1 : ContinuousAt (fun y : ℝ => logPotC (segMeasure M' h' c' N') (M + h * (y : ℂ))) x :=
    ContinuousAt.comp (g := logPotC (segMeasure M' h' c' N')) (f := fun y : ℝ => M + h * (y : ℂ))
      (x := x) (continuousAt_logPotC_seg hh' hpos' (hsep x hx)) hc
  refine h1.neg.continuousWithinAt.congr (fun y _ => ?_) ?_
  · simp [potC_eq_neg_logPotC]
  · simp [potC_eq_neg_logPotC]

/-- The own potential of `ν` is `ν`-integrable. -/
theorem integrable_potC_self {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) :
    Integrable (potC (segMeasure M h c N)) (segMeasure M h c N) := by
  haveI := isFiniteMeasure_seg (M := M) (h := h) hpos
  refine integrable_seg_of_continuousOn hpos (measurable_potC _) ?_
  have hc : ContinuousOn (fun x : ℝ => c 0 * Real.log ‖h‖ - Real.log 2 * c 0 -
      ∑ k ∈ Finset.range N, (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) /
        ((k + 1 : ℕ) : ℝ)) (Icc (-1 : ℝ) 1) := by
    refine Continuous.continuousOn ?_
    refine continuous_const.sub (continuous_finsetSum _ fun k _ => ?_)
    exact ((Polynomial.continuous _).mul continuous_const).div_const _
  exact hc.congr fun x hx => (potC_seg_inside hh hpos hx).2

/-! ### Bilinearity of the energy for two disjoint segments -/

theorem integral_pot_sum_seg {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {F P₁ P₂ : ℂ → ℝ}
    (hF : Measurable F) (h1 : Measurable P₁) (h2 : Measurable P₂)
    (hpt : ∀ x ∈ Icc (-1 : ℝ) 1, F (M + h * (x : ℂ)) = P₁ (M + h * (x : ℂ)) + P₂ (M + h * (x : ℂ)))
    (hi₁ : Integrable P₁ (segMeasure M h c N)) (hi₂ : Integrable P₂ (segMeasure M h c N)) :
    Integrable F (segMeasure M h c N) ∧
      ∫ u, F u ∂(segMeasure M h c N) =
        ∫ u, P₁ u ∂(segMeasure M h c N) + ∫ u, P₂ u ∂(segMeasure M h c N) := by
  have i1 := (integrable_segMeasure_iff hpos h1).1 hi₁
  have i2 := (integrable_segMeasure_iff hpos h2).1 hi₂
  have e : ∀ θ : ℝ, chebF c N (Real.cos θ) * F (M + h * (Real.cos θ : ℂ)) =
      chebF c N (Real.cos θ) * P₁ (M + h * (Real.cos θ : ℂ)) +
        chebF c N (Real.cos θ) * P₂ (M + h * (Real.cos θ : ℂ)) := fun θ => by
    rw [hpt _ (cos_mem θ), mul_add]
  have iF : Integrable (fun θ => chebF c N (Real.cos θ) * F (M + h * (Real.cos θ : ℂ))) arc := by
    simp_rw [e]; exact i1.add i2
  refine ⟨(integrable_segMeasure_iff hpos hF).2 iF, ?_⟩
  rw [integral_segMeasure hpos hF, integral_segMeasure hpos h1, integral_segMeasure hpos h2]
  simp_rw [e]
  exact integral_add i1 i2

theorem potC_add_at {μ ν : Measure ℂ} {t : ℂ} (h1 : Integrable (fun u => Real.log ‖t - u‖) μ)
    (h2 : Integrable (fun u => Real.log ‖t - u‖) ν) :
    potC (μ + ν) t = potC μ t + potC ν t := by
  unfold potC
  exact integral_add_measure h1 h2

/-- **W4(i), bilinearity.**  For two segment measures `ν, ν'` whose segments miss each other,
`∬ log |u - v| d(ν + ν')² = E(ν) + E(ν') + ∫ potC ν' dν + ∫ potC ν dν'`. -/
theorem energyC_add_seg {M h M' h' : ℂ} (hh : h ≠ 0) (hh' : h' ≠ 0) {c c' : ℕ → ℝ} {N N' : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hpos' : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c' N' x)
    (hsep : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M + h * (x : ℂ) - M') / h'))
    (hsep' : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M' + h' * (x : ℂ) - M) / h)) :
    energyC (segMeasure M h c N + segMeasure M' h' c' N') =
      energyC (segMeasure M h c N) + energyC (segMeasure M' h' c' N') +
        ∫ u, potC (segMeasure M' h' c' N') u ∂(segMeasure M h c N) +
        ∫ u, potC (segMeasure M h c N) u ∂(segMeasure M' h' c' N') := by
  haveI := isFiniteMeasure_seg (M := M) (h := h) hpos
  haveI := isFiniteMeasure_seg (M := M') (h := h') hpos'
  have mσ := measurable_potC (segMeasure M h c N + segMeasure M' h' c' N')
  have m1 := measurable_potC (segMeasure M h c N)
  have m2 := measurable_potC (segMeasure M' h' c' N')
  have A := integral_pot_sum_seg hpos mσ m1 m2
    (fun x hx => potC_add_at (potC_seg_inside hh hpos hx).1
      (integrable_log_seg_off hh' hpos' (hsep x hx)))
    (integrable_potC_self hh hpos) (integrable_potC_cross hh' hpos hpos' hsep)
  have B := integral_pot_sum_seg hpos' mσ m2 m1
    (fun x hx => by
      rw [add_comm (segMeasure M h c N) (segMeasure M' h' c' N')]
      rw [potC_add_at (potC_seg_inside hh' hpos' hx).1
        (integrable_log_seg_off hh hpos (hsep' x hx)), add_comm])
    (integrable_potC_self hh' hpos') (integrable_potC_cross hh hpos' hpos hsep')
  unfold energyC
  rw [integral_add_measure A.1 B.1, A.2, B.2]
  ring

/-! ### The conjugate pair `σ = s₊ + s̄₊` -/

theorem map_conj_segMeasure (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) :
    (segMeasure M h c N).map (starRingEnd ℂ) =
      segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N := by
  unfold segMeasure
  rw [Measure.map_map Complex.continuous_conj.measurable (continuous_segMap M h).measurable]
  congr 1
  funext θ
  simp only [Function.comp_apply, map_add, map_mul, Complex.conj_ofReal]

theorem potC_conj_arg (ν : Measure ℂ) (u : ℂ) :
    potC ν (starRingEnd ℂ u) = potC (ν.map (starRingEnd ℂ)) u := by
  have hm : MeasurableEmbedding (starRingEnd ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  unfold potC
  rw [hm.integral_map]
  congr 1
  funext v
  rw [← Complex.norm_conj (u - starRingEnd ℂ v)]
  simp

theorem cross_symm_conj (ν : Measure ℂ) :
    ∫ u, potC ν u ∂(ν.map (starRingEnd ℂ)) = ∫ u, potC (ν.map (starRingEnd ℂ)) u ∂ν := by
  have hm : MeasurableEmbedding (starRingEnd ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  rw [hm.integral_map]
  exact integral_congr_ae (ae_of_all _ fun u => potC_conj_arg ν u)

theorem jc_conj (z : ℂ) : jc (starRingEnd ℂ z) = jc z := by
  unfold jc
  have h1 : ‖starRingEnd ℂ z - 1‖ = ‖z - 1‖ := by
    rw [← Complex.norm_conj (z - 1)]; simp
  have h2 : ‖starRingEnd ℂ z + 1‖ = ‖z + 1‖ := by
    rw [← Complex.norm_conj (z + 1)]; simp
  rw [h1, h2]

/-- **W4 (LD14).**  For the conjugate pair `σ = s₊ + s̄₊`, `s₊ = f ω` on `{M + h x}` with the
segment off its mirror image, in the paper's sign `I = -E`:
`I(σ) = 2 I(s₊) + 2 I(s₊, s₋)`, `I(s₊) = -c₀² log(|h|/2) + Σ c_k²/(2k)`,
`I(s₊, s₋) = (1/π) ∫₀^π f(cos φ) g(φ) dφ`, `g φ = U^{s₋}(M + h cos φ) = logPotC s₋ (·)`. -/
theorem energy_conj_pair {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hsep : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M + h * (x : ℂ) - starRingEnd ℂ M) / starRingEnd ℂ h)) :
    -energyC (segMeasure M h c N + segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) =
      2 * (-(c 0 ^ 2 * (Real.log ‖h‖ - Real.log 2)) +
          ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) +
        2 * ((1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, chebF c N (Real.cos θ) *
          logPotC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N)
            (M + h * (Real.cos θ : ℂ))) := by
  have hh' : starRingEnd ℂ h ≠ 0 := (_root_.map_ne_zero (starRingEnd ℂ)).2 hh
  have hsep' : ∀ x ∈ Icc (-1 : ℝ) 1,
      1 < jc ((starRingEnd ℂ M + starRingEnd ℂ h * (x : ℂ) - M) / h) := by
    intro x hx
    have := hsep x hx
    rw [← jc_conj] at this
    convert this using 2
    simp [map_div₀, map_sub, map_add, map_mul, Complex.conj_ofReal]
  haveI := isFiniteMeasure_seg (M := M) (h := h) hpos
  have hpos' := hpos
  rw [energyC_add_seg hh hh' hpos hpos hsep hsep']
  have hE : energyC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) =
      energyC (segMeasure M h c N) := by
    rw [energyC_segMeasure hh' hpos, energyC_segMeasure hh hpos, Complex.norm_conj]
  have hX : ∫ u, potC (segMeasure M h c N) u ∂(segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) =
      ∫ u, potC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) u ∂(segMeasure M h c N) := by
    rw [← map_conj_segMeasure]
    exact cross_symm_conj _
  have hI : ∫ u, potC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) u ∂(segMeasure M h c N) =
      -((1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, chebF c N (Real.cos θ) *
        logPotC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) (M + h * (Real.cos θ : ℂ))) := by
    haveI := isFiniteMeasure_seg (M := starRingEnd ℂ M) (h := starRingEnd ℂ h) hpos
    rw [integral_segMeasure hpos (measurable_potC _), integral_arc]
    simp only [potC_eq_neg_logPotC, mul_neg]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hE, hX, hI, energyC_segMeasure hh hpos]
  ring

/-! ### The angle-variable towers: `f(cos φ)` and the curve `φ ↦ M + h cos φ` -/

/-- The derivative chain of `φ ↦ f(cos φ) = Σ_k c_k cos(kφ)`:
`d^j/dφ^j cos(kφ) = k^j cos(kφ + jπ/2)`. -/
def Ftow (c : ℕ → ℝ) (N : ℕ) (j : ℕ) (φ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), c k * (k : ℝ) ^ j * Real.cos ((k : ℝ) * φ + (j : ℝ) * (Real.pi / 2))

/-- The majorant `V_j = (Σ_k |c_k| k^j) / j!` of `|f^{(j)}| / j!` (the paper's `f_j`). -/
def Vf (c : ℕ → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (N + 1), |c k| * (k : ℝ) ^ j) / (j.factorial : ℝ)

theorem Ftow_zero (c : ℕ → ℝ) (N : ℕ) (φ : ℝ) : Ftow c N 0 φ = chebF c N (Real.cos φ) := by
  rw [chebF_cos]; unfold Ftow; simp

theorem hasDerivAt_Ftow (c : ℕ → ℝ) (N j : ℕ) (φ : ℝ) :
    HasDerivAt (Ftow c N j) (Ftow c N (j + 1) φ) φ := by
  unfold Ftow
  refine HasDerivAt.fun_sum (fun k _ => ?_)
  have h1 : HasDerivAt (fun φ : ℝ => (k : ℝ) * φ + (j : ℝ) * (Real.pi / 2)) (k : ℝ) φ := by
    simpa using ((hasDerivAt_id φ).const_mul (k : ℝ)).add_const ((j : ℝ) * (Real.pi / 2))
  have h2 := (h1.cos).const_mul (c k * (k : ℝ) ^ j)
  refine h2.congr_deriv ?_
  have e : (k : ℝ) * φ + (((j + 1 : ℕ) : ℝ)) * (Real.pi / 2) =
      ((k : ℝ) * φ + (j : ℝ) * (Real.pi / 2)) + Real.pi / 2 := by push_cast; ring
  rw [e, Real.cos_add_pi_div_two, pow_succ]
  ring

theorem isTower_Ftow (c : ℕ → ℝ) (N : ℕ) (a r : ℝ) (M : ℕ) : IsTower (Ftow c N) a r M where
  cont j _ := (continuous_iff_continuousAt.2 fun x => (hasDerivAt_Ftow c N j x).continuousAt).continuousOn
  der j _ x _ := hasDerivAt_Ftow c N j x

theorem abs_Ftow_le (c : ℕ → ℝ) (N j : ℕ) (φ : ℝ) :
    |Ftow c N j φ| / (j.factorial : ℝ) ≤ Vf c N j := by
  unfold Vf
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  unfold Ftow
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
  exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (by positivity)) (Real.abs_cos_le_one _)

theorem IsTower.mono' {f : ℕ → ℝ → ℝ} {a r a' r' : ℝ} {M : ℕ} (hf : IsTower f a' r' M)
    (h1 : a' - r' ≤ a - r) (h2 : a + r ≤ a' + r') : IsTower f a r M where
  cont j hj := (hf.cont j hj).mono (Icc_subset_Icc h1 h2)
  der j hj x hx := hf.der j hj x (Ioo_subset_Ioo h1 h2 hx)

/-- **W4(ii), one cell.**  If `G` has an order-5 tower on `[a - r, a + r]` with
`|G^{(i)}|/i! ≤ U_i` there and `Σ_{i+j=5} U_i V_j ≤ E` (`V_j = f_j`), then
`∫ G(φ) f(cos φ) dφ ≤ 2(b₀ r + b₂ r³/3 + b₄ r⁵/5) + E r⁶/3`, with `b_j` the Taylor
coefficients of `P = G · f(cos ·)` at `a`. -/
theorem cross_cell_le {Gt : ℕ → ℝ → ℝ} {c : ℕ → ℝ} {N : ℕ} {a r E : ℝ} (hr : 0 ≤ r)
    (hG : IsTower Gt a r 5) {U : ℕ → ℝ}
    (hU : ∀ x ∈ Icc (a - r) (a + r), ∀ i ≤ 5, |Gt i x| / (i.factorial : ℝ) ≤ U i)
    (hE : ∑ ij ∈ Finset.antidiagonal 5, U ij.1 * Vf c N ij.2 ≤ E) :
    ∫ x in (a - r)..(a + r), Gt 0 x * chebF c N (Real.cos x) ≤
      2 * (mulTower Gt (Ftow c N) 0 a * r + mulTower Gt (Ftow c N) 2 a / 2 * (r ^ 3 / 3) +
        mulTower Gt (Ftow c N) 4 a / 24 * (r ^ 5 / 5)) + E * (r ^ 6 / 3) := by
  have hP : IsTower (mulTower Gt (Ftow c N)) a r 5 := hG.mul (isTower_Ftow c N a r 5)
  have key := cell_integral_le (E := E) hr hP (fun x hx => by
    have hb := mulTower_block_bound (n := 5) (x := x) (u := Gt) (v := Ftow c N) (U := U)
      (V := Vf c N) (hU x hx) (fun j _ => abs_Ftow_le c N j x)
    have h5 : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
    rw [h5] at hb
    exact hb.trans hE)
  have e : (fun x => mulTower Gt (Ftow c N) 0 x) = fun x => Gt 0 x * chebF c N (Real.cos x) := by
    funext x; rw [mulTower_zero, Ftow_zero]
  have e' : (mulTower Gt (Ftow c N) 0) = fun x => Gt 0 x * chebF c N (Real.cos x) := e
  simpa [e'] using key

/-- The cell bound of `cross_cell_le`. -/
def crossCellBound (Gt : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (N : ℕ) (a r E : ℝ) : ℝ :=
  2 * (mulTower Gt (Ftow c N) 0 a * r + mulTower Gt (Ftow c N) 2 a / 2 * (r ^ 3 / 3) +
    mulTower Gt (Ftow c N) 4 a / 24 * (r ^ 5 / 5)) + E * (r ^ 6 / 3)

/-- **W4(ii), the partition.**  An exact partition `a 0 ≤ ⋯ ≤ a n` of the interval, one tower
bound per cell: `∫_{a 0}^{a n} G f(cos) ≤ Σ_i crossCellBound`. -/
theorem cross_partition_le {Gt : ℕ → ℝ → ℝ} {c : ℕ → ℝ} {N n : ℕ} {a : ℕ → ℝ}
    {Ur : ℕ → ℕ → ℝ} {Er : ℕ → ℝ}
    (hmono : ∀ i < n, a i ≤ a (i + 1))
    (hG : ∀ i < n, IsTower Gt ((a i + a (i + 1)) / 2) ((a (i + 1) - a i) / 2) 5)
    (hU : ∀ i < n, ∀ x ∈ Icc (a i) (a (i + 1)), ∀ j ≤ 5,
      |Gt j x| / (j.factorial : ℝ) ≤ Ur i j)
    (hE : ∀ i < n, ∑ ij ∈ Finset.antidiagonal 5, Ur i ij.1 * Vf c N ij.2 ≤ Er i) :
    ∫ x in (a 0)..(a n), Gt 0 x * chebF c N (Real.cos x) ≤
      ∑ i ∈ Finset.range n, crossCellBound Gt c N ((a i + a (i + 1)) / 2) ((a (i + 1) - a i) / 2)
        (Er i) := by
  have e1 : ∀ i, (a i + a (i + 1)) / 2 - (a (i + 1) - a i) / 2 = a i := fun i => by ring
  have e2 : ∀ i, (a i + a (i + 1)) / 2 + (a (i + 1) - a i) / 2 = a (i + 1) := fun i => by ring
  refine partition_integral_le n (f := fun x => Gt 0 x * chebF c N (Real.cos x)) ?_ ?_
  · intro i hi
    have hc := (hG i hi).cont 0 (by norm_num)
    rw [e1, e2] at hc
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (hmono i hi)]
    exact hc.mul (continuous_chebF_cos c N).continuousOn
  · intro i hi
    have h := cross_cell_le (c := c) (N := N) (hr := by linarith [hmono i hi]) (hG i hi)
      (U := Ur i) (E := Er i) (fun x hx j hj => hU i hi x (by rw [e1, e2] at hx; exact hx) j hj)
      (hE i hi)
    rw [e1, e2] at h
    exact h

/-! ### The cross energy of the conjugate pair over an exact cell partition -/

/-- The derivative chain of `φ ↦ M + h cos φ`. -/
def cosCurve (M h : ℂ) (i : ℕ) (x : ℝ) : ℂ :=
  (if i = 0 then M else 0) + h * ((Real.cos (x + (i : ℝ) * (Real.pi / 2)) : ℝ) : ℂ)

theorem cosCurve_zero (M h : ℂ) (x : ℝ) : cosCurve M h 0 x = M + h * (Real.cos x : ℂ) := by
  simp [cosCurve]

theorem hasDerivAt_cosCurve (M h : ℂ) (i : ℕ) (x : ℝ) :
    HasDerivAt (cosCurve M h i) (cosCurve M h (i + 1) x) x := by
  unfold cosCurve
  have h1 : HasDerivAt (fun y : ℝ => Real.cos (y + (i : ℝ) * (Real.pi / 2)))
      (-Real.sin (x + (i : ℝ) * (Real.pi / 2))) x := by
    simpa using ((hasDerivAt_id x).add_const ((i : ℝ) * (Real.pi / 2))).cos
  have h2 := (h1.ofReal_comp).const_mul h
  have h3 := h2.const_add (if i = 0 then M else 0)
  refine h3.congr_deriv ?_
  have e : x + (((i + 1 : ℕ) : ℝ)) * (Real.pi / 2) = (x + (i : ℝ) * (Real.pi / 2)) + Real.pi / 2 := by
    push_cast; ring
  rw [e, Real.cos_add_pi_div_two]
  simp

/-- **LD13 for the cross energy.**  The order-5 tower of `φ ↦ U^{s₋}(M + h cos φ)` on a cell
(`s₋` the segment `(M', h')` with measure `f ω`), whenever the curve stays off that segment. -/
theorem isTower_cross {M h M' h' : ℂ} (hh' : h' ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hsep : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M + h * (x : ℂ) - M') / h')) (a r : ℝ) :
    IsTower (potT M' h' c N (cosCurve M h)) a r 5 :=
  isTower_potT hh' hpos (fun i _ x => hasDerivAt_cosCurve M h i x)
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_cosCurve M h 5 x).continuousAt)
    (fun x _ => by rw [cosCurve_zero]; exact hsep _ (cos_mem x))

/-- **W4 (LD14), the certified upper bound.**  For the conjugate pair `σ = s₊ + s̄₊` (segment off
its mirror image), an exact partition `0 = a₀ ≤ ⋯ ≤ a_n = π` of the angle, and per cell
bounds `|G^{(j)}|/j! ≤ U_{ij}` of the order-≤5 tower of `G φ = U^{s₋}(M + h cos φ)` with
`Σ_{i+j=5} U_{ii'} f_j ≤ E_i`:
`I(σ) ≤ 2 I(s₊) + (2/π) Σ_cells [2(b₀ r + b₂ r³/3 + b₄ r⁵/5) + E r⁶/3]`. -/
theorem energy_conj_pair_le {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hsep : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M + h * (x : ℂ) - starRingEnd ℂ M) / starRingEnd ℂ h))
    {n : ℕ} {a : ℕ → ℝ} (a0 : a 0 = 0) (an : a n = Real.pi)
    (hmono : ∀ i < n, a i ≤ a (i + 1)) {Ur : ℕ → ℕ → ℝ} {Er : ℕ → ℝ}
    (hU : ∀ i < n, ∀ x ∈ Icc (a i) (a (i + 1)), ∀ j ≤ 5,
      |potT (starRingEnd ℂ M) (starRingEnd ℂ h) c N (cosCurve M h) j x| / (j.factorial : ℝ) ≤ Ur i j)
    (hE : ∀ i < n, ∑ ij ∈ Finset.antidiagonal 5, Ur i ij.1 * Vf c N ij.2 ≤ Er i) :
    -energyC (segMeasure M h c N + segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) ≤
      2 * (-(c 0 ^ 2 * (Real.log ‖h‖ - Real.log 2)) +
          ∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) +
        2 * ((1 / Real.pi) * ∑ i ∈ Finset.range n,
          crossCellBound (potT (starRingEnd ℂ M) (starRingEnd ℂ h) c N (cosCurve M h)) c N
            ((a i + a (i + 1)) / 2) ((a (i + 1) - a i) / 2) (Er i)) := by
  have hh' : starRingEnd ℂ h ≠ 0 := (_root_.map_ne_zero (starRingEnd ℂ)).2 hh
  rw [energy_conj_pair hh hpos hsep]
  have hpart := cross_partition_le (c := c) (N := N) (n := n) (a := a) (Ur := Ur) (Er := Er)
    (Gt := potT (starRingEnd ℂ M) (starRingEnd ℂ h) c N (cosCurve M h)) hmono
    (fun i _ => isTower_cross hh' hpos hsep _ _) hU hE
  rw [a0, an] at hpart
  have hg : ∀ θ : ℝ, chebF c N (Real.cos θ) *
      logPotC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) (M + h * (Real.cos θ : ℂ)) =
      potT (starRingEnd ℂ M) (starRingEnd ℂ h) c N (cosCurve M h) 0 θ * chebF c N (Real.cos θ) := by
    intro θ
    simp only [potT, if_true, cosCurve_zero]
    ring
  simp_rw [hg]
  have hπ : 0 ≤ 1 / Real.pi := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpart hπ]

/-- For `i ≥ 1` the curve derivatives satisfy `‖γ_i‖ ≤ ‖h‖`. -/
theorem norm_cosCurve_le (M h : ℂ) {i : ℕ} (hi : 1 ≤ i) (x : ℝ) : ‖cosCurve M h i x‖ ≤ ‖h‖ := by
  unfold cosCurve
  rw [if_neg (by omega), zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

/-- **LD13 order-5 remainder for the cross term.**  The `U_5` entry of the cell data:
`|G^{(5)}|/5! ≤ fdbBound(k ↦ (k-1)! c₀ / d_lo^k, i ↦ |h|)/120`, given the distance bound
`d_lo ≤ |h'|(c(ζ) - 1)` from the segment `(M', h')`. -/
theorem cross_U5_le {M h M' h' : ℂ} (hh' : h' ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hsep : ∀ x ∈ Icc (-1 : ℝ) 1, 1 < jc ((M + h * (x : ℂ) - M') / h'))
    {x dlo : ℝ} (hdlo0 : 0 < dlo)
    (hdlo : dlo ≤ ‖h'‖ * (jc ((M + h * (Real.cos x : ℂ) - M') / h') - 1)) :
    |potT M' h' c N (cosCurve M h) 5 x| / ((5 : ℕ).factorial : ℝ) ≤
      fdbBound (fun k => ((k - 1).factorial : ℝ) * c 0 / dlo ^ k) (fun _ => ‖h‖) / 120 := by
  have h5 : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [h5]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine abs_potT5_le hh' hpos (x := x) (dlo := dlo) ?_ hdlo0 ?_ (fun i hi _ => norm_cosCurve_le M h hi x)
  · rw [cosCurve_zero]; exact hsep _ (cos_mem x)
  · rw [cosCurve_zero]; exact hdlo
end

end CatalanCore.Lai.DecayEnergy
