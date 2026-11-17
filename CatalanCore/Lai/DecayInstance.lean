module

public import CatalanCore.Lai.DecayDual
public import CatalanCore.Lai.DecayCells
public import CatalanCore.Zeta5.Potential.Measure
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

/-!
# Lai decay at the two-arcsine-segment measure (LD10)

`lai_decay_instance`: Theorem A for Lai's family (`lai_decay_dual`, rerun in the n-scaled form
`lai_decay_dual_S`) at `σ = s₊ + s̄₊`, `s₊ = f dω` on the arm segment `[A₀, A₁]` of the wedge polyline
`x₀ = 8/5 → P = 21/10 + (11/5) i`, then the vertical ray.

* `sig2`, `ballMajA_sig2`: the measure, its mass `2 c₀`, conjugation symmetry, the `√`-majorant;
* `PieceGoodS`, `curve_good_S`, `lai_decay_dual_S`: `lai_decay_dual` with the piece constant `n Cfin`
  (the pieces of the n-scaled polygon have `‖D‖ ~ n`);
* `LaiCover`: the chained outputs of `cellA/G/R_sound` (the cell checks are data);
* `near_vertex`, `arm_cover`: `W_σ ≤ ℓ + η` on a neighbourhood of the vertex and `W_σ ≤ ℓ` on the arm;
* `lai_hcont`: the polygon `v → v + i → nq → nP → nT → ∞ i`;
* `lai_decay_instance`: the decay bound.

Say μ, never B, for the irrationality measure; `B` below is the design parameter.
-/

open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayInstance

open CatalanCore.Lai CatalanCore.Lai.DecayDual CatalanCore.Lai.DecayCells
  CatalanCore.Decay.LemmaW CatalanCore.Decay.ComplexContour CatalanCore.Lai.DecayContour
  CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexEnergy CatalanCore.Decay.WedgeBounds
  CatalanCore.Tools.Joukowski CatalanCore.Decay.CurveFamily CatalanCore.Decay.ComplexTaylor
open CatalanCore.Zeta5.Potential (arc chebF tmap omega omega_Icc_le abs_chebF_le cos_mem
  continuous_tmap integrable_chebF integral_chebF)

/-! ### 1. The segment measure: mass, support, ball bound, conjugation -/

theorem segMeasure_univ {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) :
    segMeasure M h c N univ = ENNReal.ofReal (c 0) := by
  unfold segMeasure
  rw [Measure.map_apply (continuous_segMap M h).measurable MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_chebF c N)
      (ae_of_all _ fun θ => hpos _ (cos_mem θ)), integral_chebF]

theorem isFiniteMeasure_segMeasure {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) : IsFiniteMeasure (segMeasure M h c N) :=
  ⟨by rw [segMeasure_univ hpos]; exact ENNReal.ofReal_lt_top⟩

theorem segMeasure_compl {M h : ℂ} {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : ‖M‖ + ‖h‖ ≤ b) :
    segMeasure M h c N (Metric.closedBall (0 : ℂ) b)ᶜ = 0 := by
  unfold segMeasure
  rw [Measure.map_apply (continuous_segMap M h).measurable
    Metric.isClosed_closedBall.measurableSet.compl]
  have : (fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' (Metric.closedBall (0 : ℂ) b)ᶜ = ∅ := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le,
      mem_empty_iff_false, iff_false, not_lt]
    calc ‖M + h * (Real.cos θ : ℂ)‖ ≤ ‖M‖ + ‖h * (Real.cos θ : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖M‖ + ‖h‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add le_rfl (mul_le_of_le_one_right (norm_nonneg h) (Real.abs_cos_le_one θ))
      _ ≤ b := hb
  rw [this]
  simp

/-- The arcsine mass of a ball: `s(B(c₀, r)) ≤ (∑ |c_k|) √(r / ‖h‖)`. -/
theorem segMeasure_ball_le {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ} (c0 : ℂ) {r : ℝ}
    (hr : 0 ≤ r) :
    segMeasure M h c N (Metric.closedBall c0 r) ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range (N + 1), |c k|) * Real.sqrt (r / ‖h‖)) := by
  have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hF0 : 0 ≤ ∑ k ∈ Finset.range (N + 1), |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hρ0 : 0 ≤ r / ‖h‖ := div_nonneg hr hhn.le
  have hS : MeasurableSet ((fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' Metric.closedBall c0 r) :=
    (continuous_segMap M h).measurable Metric.isClosed_closedBall.measurableSet
  have hsub : (fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' Metric.closedBall c0 r ⊆
      tmap 2 ⁻¹' Icc (1 + ((c0 - M) / h).re - r / ‖h‖) (1 + ((c0 - M) / h).re + r / ‖h‖) := by
    intro θ hθ
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] at hθ
    simp only [Set.mem_preimage, Set.mem_Icc]
    have e : M + h * (Real.cos θ : ℂ) - c0 = h * ((Real.cos θ : ℂ) - (c0 - M) / h) := by
      first
        | (field_simp; ring)
        | field_simp
    rw [e, norm_mul] at hθ
    have h1 : ‖(Real.cos θ : ℂ) - (c0 - M) / h‖ ≤ r / ‖h‖ := by
      rw [le_div_iff₀ hhn]
      linarith [mul_comm ‖h‖ ‖(Real.cos θ : ℂ) - (c0 - M) / h‖]
    have h2 : |Real.cos θ - ((c0 - M) / h).re| ≤ r / ‖h‖ := by
      have := Complex.abs_re_le_norm ((Real.cos θ : ℂ) - (c0 - M) / h)
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      exact this.trans h1
    have h3 := abs_le.mp h2
    unfold tmap
    constructor <;> nlinarith [h3.1, h3.2]
  unfold segMeasure
  rw [Measure.map_apply (continuous_segMap M h).measurable
    Metric.isClosed_closedBall.measurableSet, withDensity_apply _ hS]
  calc ∫⁻ θ in (fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' Metric.closedBall c0 r,
        ENNReal.ofReal (chebF c N (Real.cos θ)) ∂arc
      ≤ ∫⁻ _θ in (fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' Metric.closedBall c0 r,
        ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) ∂arc := by
        refine lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_
        exact (le_abs_self _).trans (abs_chebF_le c N (cos_mem θ))
    _ = ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) *
          arc ((fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' Metric.closedBall c0 r) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) *
          ENNReal.ofReal (Real.sqrt (r / ‖h‖)) := by
        refine mul_le_mul' le_rfl ?_
        calc arc ((fun θ : ℝ => M + h * (Real.cos θ : ℂ)) ⁻¹' Metric.closedBall c0 r)
            ≤ arc (tmap 2 ⁻¹' Icc (1 + ((c0 - M) / h).re - r / ‖h‖)
                (1 + ((c0 - M) / h).re + r / ‖h‖)) := measure_mono hsub
          _ = omega 2 (Icc (1 + ((c0 - M) / h).re - r / ‖h‖) (1 + ((c0 - M) / h).re + r / ‖h‖)) := by
              unfold omega
              rw [Measure.map_apply (continuous_tmap 2).measurable measurableSet_Icc]
          _ ≤ ENNReal.ofReal (Real.sqrt (2 * (r / ‖h‖) / 2)) := omega_Icc_le two_pos _ _
          _ = ENNReal.ofReal (Real.sqrt (r / ‖h‖)) := by
              rw [show 2 * (r / ‖h‖) / 2 = r / ‖h‖ by ring]
    _ = _ := by rw [← ENNReal.ofReal_mul hF0]

theorem map_conj_segMeasure (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) :
    (segMeasure M h c N).map (starRingEnd ℂ) =
      segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N := by
  unfold segMeasure
  rw [Measure.map_map Complex.continuous_conj.measurable (continuous_segMap M h).measurable]
  have : (starRingEnd ℂ ∘ fun θ : ℝ => M + h * (Real.cos θ : ℂ)) =
      fun θ : ℝ => starRingEnd ℂ M + starRingEnd ℂ h * (Real.cos θ : ℂ) := by
    funext θ
    simp only [Function.comp_apply, map_add, map_mul, Complex.conj_ofReal]
  rw [this]

/-- The measure `σ = s + s̄` of two conjugate arcsine segments. -/
noncomputable def sig2 (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) : Measure ℂ :=
  segMeasure M h c N + segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N

theorem sig2_conj (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) :
    (sig2 M h c N).map (starRingEnd ℂ) = sig2 M h c N := by
  unfold sig2
  rw [Measure.map_add _ _ Complex.continuous_conj.measurable, map_conj_segMeasure,
    map_conj_segMeasure, Complex.conj_conj, Complex.conj_conj, add_comm]

theorem isFiniteMeasure_sig2 {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) : IsFiniteMeasure (sig2 M h c N) := by
  haveI := isFiniteMeasure_segMeasure (M := M) (h := h) hpos
  haveI := isFiniteMeasure_segMeasure (M := starRingEnd ℂ M) (h := starRingEnd ℂ h) hpos
  unfold sig2
  infer_instance

theorem sig2_real_univ {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (hc0 : 0 ≤ c 0) :
    (sig2 M h c N).real univ = 2 * c 0 := by
  unfold sig2 Measure.real
  rw [Measure.add_apply, segMeasure_univ hpos, segMeasure_univ hpos,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc0]
  ring

theorem ballMajA_sig2 {M h : ℂ} (hh : h ≠ 0) (c : ℕ → ℝ) (N : ℕ) :
    BallMajA (sig2 M h c N) (‖M‖ + ‖h‖ + 1)
      (2 * (∑ k ∈ Finset.range (N + 1), |c k|) / Real.sqrt ‖h‖) (1 / 2) where
  b_pos := by positivity
  A_nonneg := by positivity
  α_pos := by norm_num
  supp := by
    have s1 : segMeasure M h c N (Metric.closedBall (0 : ℂ) (‖M‖ + ‖h‖ + 1))ᶜ = 0 :=
      segMeasure_compl (by linarith [norm_nonneg M, norm_nonneg h])
    have s2 : segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N
        (Metric.closedBall (0 : ℂ) (‖M‖ + ‖h‖ + 1))ᶜ = 0 :=
      segMeasure_compl (by simp only [Complex.norm_conj]; linarith [norm_nonneg M, norm_nonneg h])
    unfold sig2
    rw [Measure.add_apply, s1, s2, add_zero]
  maj := by
    intro c0 r hr
    have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hF0 : 0 ≤ ∑ k ∈ Finset.range (N + 1), |c k| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    unfold sig2
    rw [Measure.add_apply]
    have h1 := segMeasure_ball_le (M := M) hh (c := c) (N := N) c0 hr
    have h2 := segMeasure_ball_le (M := starRingEnd ℂ M) (h := starRingEnd ℂ h)
      (by simpa using hh) (c := c) (N := N) c0 hr
    rw [Complex.norm_conj] at h2
    have e : 2 * (∑ k ∈ Finset.range (N + 1), |c k|) / Real.sqrt ‖h‖ * r ^ (1 / 2 : ℝ) =
        (∑ k ∈ Finset.range (N + 1), |c k|) * Real.sqrt (r / ‖h‖) +
          (∑ k ∈ Finset.range (N + 1), |c k|) * Real.sqrt (r / ‖h‖) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div hr]
      ring
    rw [e, ENNReal.ofReal_add (mul_nonneg hF0 (Real.sqrt_nonneg _))
      (mul_nonneg hF0 (Real.sqrt_nonneg _))]
    exact add_le_add h1 h2

/-- A property of all points of the two segments holds `σ`-almost everywhere. -/
theorem ae_sig2 {M h : ℂ} {c : ℕ → ℝ} {N : ℕ} (P : ℂ → Prop) (hm : MeasurableSet {u | ¬ P u})
    (hP : ∀ θ : ℝ, P (M + h * (Real.cos θ : ℂ)))
    (hQ : ∀ θ : ℝ, P (starRingEnd ℂ M + starRingEnd ℂ h * (Real.cos θ : ℂ))) :
    ∀ᵐ u ∂(sig2 M h c N), P u := by
  have h0 : ∀ (M' h' : ℂ), (∀ θ : ℝ, P (M' + h' * (Real.cos θ : ℂ))) →
      segMeasure M' h' c N {u | ¬ P u} = 0 := by
    intro M' h' hP'
    unfold segMeasure
    rw [Measure.map_apply (continuous_segMap M' h').measurable hm]
    have : (fun θ : ℝ => M' + h' * (Real.cos θ : ℂ)) ⁻¹' {u | ¬ P u} = ∅ := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      exact hP' θ
    rw [this]
    simp
  rw [ae_iff]
  unfold sig2
  rw [Measure.add_apply, h0 M h hP, h0 _ _ hQ, add_zero]

/-! ### 2. Lai's concrete geometry -/

noncomputable def laiX0 : ℂ := ⟨8 / 5, 0⟩
noncomputable def laiP : ℂ := ⟨21 / 10, 11 / 5⟩
noncomputable def laiT : ℂ := ⟨21 / 10, 33 / 10⟩
noncomputable def laiM : ℂ := ⟨737 / 400, 1067 / 1000⟩
noncomputable def laiH : ℂ := ⟨93 / 400, 1023 / 1000⟩

@[simp] theorem laiX0_re : laiX0.re = 8 / 5 := rfl
@[simp] theorem laiX0_im : laiX0.im = 0 := rfl
@[simp] theorem laiP_re : laiP.re = 21 / 10 := rfl
@[simp] theorem laiP_im : laiP.im = 11 / 5 := rfl
@[simp] theorem laiT_re : laiT.re = 21 / 10 := rfl
@[simp] theorem laiT_im : laiT.im = 33 / 10 := rfl
@[simp] theorem laiM_re : laiM.re = 737 / 400 := rfl
@[simp] theorem laiM_im : laiM.im = 1067 / 1000 := rfl
@[simp] theorem laiH_re : laiH.re = 93 / 400 := rfl
@[simp] theorem laiH_im : laiH.im = 1023 / 1000 := rfl

theorem laiH_ne : laiH ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  rw [laiH_re] at h1
  norm_num at h1

/-- The measure of Lai's design: `s₊ + s̄₊`, `s₊ = f dω` on `[A₀, A₁]`. -/
noncomputable abbrev laiSigma (c : ℕ → ℝ) (N : ℕ) : Measure ℂ := sig2 laiM laiH c N

/-- The threshold `ℓ` of the wedge certificate. -/
noncomputable abbrev laiEll : ℝ := -130471 / 10000

theorem norm_le_of_coords {z : ℂ} {b : ℝ} (hb : 0 ≤ b) (h : z.re ^ 2 + z.im ^ 2 ≤ b ^ 2) :
    ‖z‖ ≤ b := by
  have h1 : ‖z‖ ^ 2 ≤ b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h1 hb)

/-- Real and imaginary parts of the explicit complex numbers of the design. -/
local macro "csimp" : tactic =>
  `(tactic| simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, laiX0_re, laiX0_im, laiP_re, laiP_im, laiT_re, laiT_im,
    laiM_re, laiM_im, laiH_re, laiH_im])

theorem laiSigma_re_ae (c : ℕ → ℝ) (N : ℕ) : ∀ᵐ u ∂(laiSigma c N), (8 / 5 : ℝ) ≤ u.re := by
  refine ae_sig2 (fun u : ℂ => (8 / 5 : ℝ) ≤ u.re) ?_ ?_ ?_
  · exact (measurableSet_le measurable_const Complex.measurable_re).compl
  · intro θ
    have := Real.neg_one_le_cos θ
    show (8 / 5 : ℝ) ≤ (laiM + laiH * (Real.cos θ : ℂ)).re
    csimp
    linarith
  · intro θ
    have := Real.neg_one_le_cos θ
    show (8 / 5 : ℝ) ≤ (starRingEnd ℂ laiM + starRingEnd ℂ laiH * (Real.cos θ : ℂ)).re
    csimp
    linarith

theorem laiSigma_disc_ae (c : ℕ → ℝ) (N : ℕ) :
    ∀ᵐ u ∂(laiSigma c N), ‖(((21 / 10 : ℝ)) : ℂ) - u‖ ≤ 2091 / 1000 := by
  have hmeas : Measurable fun u : ℂ => ‖(((21 / 10 : ℝ)) : ℂ) - u‖ :=
    (measurable_const.sub measurable_id).norm
  refine ae_sig2 (fun u : ℂ => ‖(((21 / 10 : ℝ)) : ℂ) - u‖ ≤ 2091 / 1000) ?_ ?_ ?_
  · exact (measurableSet_le hmeas measurable_const).compl
  · intro θ
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    have h3 : 0 ≤ (1 - Real.cos θ) * (1 + Real.cos θ) := mul_nonneg (by linarith) (by linarith)
    show ‖(((21 / 10 : ℝ)) : ℂ) - (laiM + laiH * (Real.cos θ : ℂ))‖ ≤ 2091 / 1000
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    nlinarith [h3]
  · intro θ
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    have h3 : 0 ≤ (1 - Real.cos θ) * (1 + Real.cos θ) := mul_nonneg (by linarith) (by linarith)
    show ‖(((21 / 10 : ℝ)) : ℂ) -
      (starRingEnd ℂ laiM + starRingEnd ℂ laiH * (Real.cos θ : ℂ))‖ ≤ 2091 / 1000
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    nlinarith [h3]

theorem laiSigma_hint {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] {bb A : ℝ}
    (hσ : BallMajA (laiSigma c N) bb A (1 / 2)) :
    ∀ x ∈ Icc (0 : ℝ) 6, Integrable (fun u => Real.log ‖(x : ℂ) + u‖) (laiSigma c N) := by
  intro x _
  refine (integrable_log_norm_sub hσ (-(x : ℂ))).congr (Filter.Eventually.of_forall fun u => ?_)
  show Real.log ‖-(x : ℂ) - u‖ = Real.log ‖(x : ℂ) + u‖
  rw [show -(x : ℂ) - u = -((x : ℂ) + u) by ring, norm_neg]

theorem laiSigma_hint1 {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] :
    Integrable (fun u => ln1 u (2211 / 500)) (laiSigma c N) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · unfold ln1
    exact ((measurable_const.add Complex.measurable_re).div
      (((measurable_const.add Complex.measurable_re).pow_const 2).add
        (Complex.measurable_im.pow_const 2))).aestronglyMeasurable
  · filter_upwards [laiSigma_re_ae c N] with u hu
    unfold ln1
    have ha : (1 : ℝ) ≤ 2211 / 500 + u.re := by linarith
    have hb : 0 < (2211 / 500 + u.re) ^ 2 + u.im ^ 2 := by
      nlinarith [sq_nonneg u.im, mul_pos (show (0 : ℝ) < 2211 / 500 + u.re by linarith)
        (show (0 : ℝ) < 2211 / 500 + u.re by linarith)]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hb.le), div_le_one hb]
    nlinarith [sq_nonneg u.im, sq_nonneg (2211 / 500 + u.re - 1)]

/-! ### 3. The scaled dual theorem -/

/-- The piece hypothesis of the n-scaled polygon: finite pieces have `‖D‖ ~ n`. -/
def PieceGoodS (σ : Measure ℂ) (n : ℕ) (ℓ' Cfin : ℝ) (p : Piece) : Prop :=
  (p.ray = false → ∃ Rs : ℝ, PieceOK σ n ℓ' Rs p ∧
    ‖p.D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 ≤ (n : ℝ) * Cfin) ∧
  (p.ray = true → ‖p.D‖ = 1 ∧ RayOK σ n ℓ' (1 / 40) (27 / 5) p)

theorem PieceGoodS.conj {σ : Measure ℂ} (hσ : σ.map (starRingEnd ℂ) = σ) {n : ℕ} {ℓ' Cfin : ℝ}
    {p : Piece} (h : PieceGoodS σ n ℓ' Cfin p) : PieceGoodS σ n ℓ' Cfin p.conj := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨Rs, h1, h2⟩ := h.1 hr
    refine ⟨Rs, PieceOK.conj hσ h1, ?_⟩
    simpa [Piece.conj] using h2
  · obtain ⟨h1, h2⟩ := h.2 hr
    refine ⟨?_, RayOK.conj hσ h2⟩
    simpa [Piece.conj] using h1

/-- **Per-curve facts, n-scaled constants**: the factor `n` of `‖D‖` is absorbed by
`n ≤ e^{nκ}/κ`. -/
theorem curve_good_S (σ : Measure ℂ) [IsFiniteMeasure σ] {bb A : ℝ}
    (hσ : BallMajA σ bb A (1 / 2)) (a b : ℝ) (hlam : 0 < 3 * |a| + |b|) {n : ℕ} (hn : 1 ≤ n)
    {ℓ' κ Cfin Cr : ℝ} (hκ : 0 < κ)
    (hCr : ∀ p : Piece, p.ray = true → ‖p.D‖ = 1 → RayOK σ n (ℓ' + κ) (1 / 40) (27 / 5) p →
      ∀ κ' : ℂ, ‖κ'‖ = (2 * Real.pi)⁻¹ →
      CurveBd σ n (Curve.ofPiece κ' (rhoT n a b) p) (Cr * (n : ℝ) ^ 4 * Real.exp (n * (ℓ' + κ))))
    {p : Piece} (hp : PieceGoodS σ n ℓ' Cfin p) {κ' : ℂ} (hκ' : ‖κ'‖ = (2 * Real.pi)⁻¹) :
    CurveBd σ n (Curve.ofPiece κ' (rhoT n a b) p)
        (max (max Cfin 0 / κ) Cr * (n : ℝ) ^ 4 * Real.exp (n * (ℓ' + κ))) ∧
      ∀ k : ℕ, Integrable (fun t : ℝ => (Curve.ofPiece κ' (rhoT n a b) p).w t *
        (Curve.ofPiece κ' (rhoT n a b) p).ζ t ^ k) (Curve.ofPiece κ' (rhoT n a b) p).ν := by
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  cases hray : p.ray
  · obtain ⟨Rs, hOK, hle⟩ := hp.1 hray
    refine ⟨(curveBd_seg σ a b hlam hn hray hOK hκ').mono ?_, fun k => ?_⟩
    · have hexp : Real.exp (n * (ℓ' + κ)) = Real.exp (n * ℓ') * Real.exp (n * κ) := by
        rw [mul_add, Real.exp_add]
      have hnk : (n : ℝ) ≤ Real.exp (n * κ) / κ := by
        rw [le_div_iff₀ hκ]
        have := Real.add_one_le_exp ((n : ℝ) * κ)
        nlinarith
      have hE := (Real.exp_pos (n * ℓ')).le
      have hC0 : (0 : ℝ) ≤ max Cfin 0 := le_max_right _ _
      calc ‖p.D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 *
            (n : ℝ) ^ 4 * Real.exp (n * ℓ')
          ≤ (n : ℝ) * Cfin * (n : ℝ) ^ 4 * Real.exp (n * ℓ') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hn4) hE
        _ ≤ (n : ℝ) * max Cfin 0 * (n : ℝ) ^ 4 * Real.exp (n * ℓ') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_left Cfin 0) hn0.le) hn4) hE
        _ ≤ (Real.exp (n * κ) / κ) * max Cfin 0 * (n : ℝ) ^ 4 * Real.exp (n * ℓ') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hnk hC0) hn4) hE
        _ = (max Cfin 0 / κ) * (n : ℝ) ^ 4 * Real.exp (n * (ℓ' + κ)) := by
            rw [hexp]
            ring
        _ ≤ max (max Cfin 0 / κ) Cr * (n : ℝ) ^ 4 * Real.exp (n * (ℓ' + κ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hn4)
              (Real.exp_pos _).le
    · refine (integrable_finite_piece hσ κ' n a b p hray (M := ‖p.D‖ * (2 * Real.pi)⁻¹ *
        EB n ℓ' Rs) (fun t ht => piece_pt_le σ a b hlam hn hOK hκ' ht) k).2
  · obtain ⟨hD, hR⟩ := hp.2 hray
    have hR' := hR.mono_ell (show ℓ' ≤ ℓ' + κ by linarith)
    refine ⟨(hCr p hray hD hR' κ' hκ').mono ?_, fun k => ?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hn4)
        (Real.exp_pos _).le
    · obtain ⟨M, hM⟩ := ray_curveG_le σ a b hlam hn (by norm_num : (0 : ℝ) < 1 / 40)
        (by norm_num : (0 : ℝ) ≤ 27 / 5) hD hR hκ'
      exact (integrable_ray_piece hσ κ' n a b p hray (M := M) (μ := 1 / 40 / 2) (by norm_num)
        (fun t ht => hM t ht) k).2

/-- **LD09, n-scaled form.**  Same as `lai_decay_dual`, with the piece constant `n * Cfin`. -/
theorem lai_decay_dual_S {σ : Measure ℂ} [IsFiniteMeasure σ] {bb A : ℝ}
    (hσ : BallMajA σ bb A (1 / 2)) (hmass : σ.real univ = 3)
    (hconj : σ.map (starRingEnd ℂ) = σ) {ℓ ρ astar : ℝ} (hρ : astar ≤ ℓ + ρ)
    (hat : ∀ x ∈ Icc (0 : ℝ) 6, omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ astar)
    (hcont : ∀ η : ℝ, 0 < η → ∃ (N K : ℕ) (Cfin : ℝ), ∀ n : ℕ, N ≤ n → ∃ (v : ℝ) (pts : List ℂ),
      0 < v ∧ v < 2 * n + 1 ∧ (∀ m : ℤ, v ≠ m) ∧ (∀ z ∈ pts, 0 < z.im) ∧ pts.length ≤ K ∧
      ∀ p ∈ laiPieces v pts Complex.I, PieceGoodS σ n (ℓ + η) Cfin p) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ n : ℕ, R₀ ≤ n → ∀ a b t : ℝ, 0 < laiLam a b →
      |t| ≤ laiLam a b * Real.exp (-(ρ * n)) →
      |MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n)| ≤
        laiLam a b ^ (3 * n) * Real.exp (-(-((3 : ℝ) ^ 2 * (3 / 2 - Real.log 3) - energyC σ +
          3 * ℓ) - ε) * (n : ℝ) ^ 2) := by
  intro ε hε
  have hη : 0 < ε / 12 := by positivity
  obtain ⟨N, K, Cfin, hN⟩ := hcont (ε / 12) hη
  obtain ⟨Cr, hCr0, hCr⟩ := curveBd_ray (δ := 1 / 40) (R0 := 27 / 5) (by norm_num) (by norm_num)
  have hCmax0 : 0 ≤ max (max Cfin 0 / (ε / 12)) Cr := hCr0.trans (le_max_right _ _)
  set Cmax : ℝ := max (max Cfin 0 / (ε / 12)) Cr with hCmax
  set Ctot : ℝ := Cmax * (2 * ((K : ℝ) + 1)) + 7 * 6 with hCtot
  have hCtot0 : 0 < Ctot := by positivity
  obtain ⟨R1, hR1⟩ := CatalanCore.Decay.TheoremA.theoremA_eventually hσ hmass
    (by norm_num : (0 : ℝ) < 3) (ℓ + ε / 12 + ε / 12) 4 (Real.log Ctot) (ε := ε / 2) (half_pos hε)
  refine ⟨max R1 (max N 1), fun n hn a b t hlam ht => ?_⟩
  have hnR : R1 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn1 : 1 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨v, pts, hv0, hv2, hvm, hpts, hlen, hP⟩ := hN n hnN
  have hd : 0 < (Complex.I).im := by simp
  set α : ℕ → ℂ := fun k => (((6 * t * (laiCoef n k : ℝ) / laiLam a b : ℝ)) : ℂ) with hα
  set Pcs : List Curve := (laiPieces v pts Complex.I).map (Curve.ofPiece (-CatalanCore.Lai.DecayDual.kap) (rhoT n a b)) ++
    ((laiPieces v pts Complex.I).map Piece.conj).map (Curve.ofPiece CatalanCore.Lai.DecayDual.kap (rhoT n a b)) with hPcs
  have hcs : laiCurves n a b t v pts Complex.I = Pcs ++ atomCurves n α := rfl
  have hCr' : ∀ p : Piece, p.ray = true → ‖p.D‖ = 1 →
      RayOK σ n (ℓ + ε / 12 + ε / 12) (1 / 40) (27 / 5) p →
      ∀ κ : ℂ, ‖κ‖ = (2 * Real.pi)⁻¹ →
      CurveBd σ n (Curve.ofPiece κ (rhoT n a b) p)
        (Cr * (n : ℝ) ^ 4 * Real.exp (n * (ℓ + ε / 12 + ε / 12))) :=
    fun p h1 h2 h3 κ hκ => hCr σ a b hlam n hn1 (ℓ + ε / 12 + ε / 12) p h1 h2 h3 κ hκ
  have hgood : ∀ c ∈ Pcs, CurveBd σ n c (Cmax * (n : ℝ) ^ 4 * Real.exp (n * (ℓ + ε / 12 + ε / 12))) ∧
      ∀ k : ℕ, Integrable (fun s : ℝ => c.w s * c.ζ s ^ k) c.ν := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact curve_good_S σ hσ a b hlam hn1 hη hCr' (hP p hp) norm_neg_kap
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact curve_good_S σ hσ a b hlam hn1 hη hCr' (PieceGoodS.conj hconj (hP p hp)) norm_kap
  have hα' : ∀ k ≤ 6 * n, ‖α k‖ ≤ 6 * Real.exp (-(ρ * n)) * (laiCoef n k : ℝ) := by
    intro k _
    have hc0 : (0 : ℝ) ≤ (laiCoef n k : ℝ) := Nat.cast_nonneg _
    simp only [hα]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlam, div_le_iff₀ hlam,
      abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 6 * (laiCoef n k : ℝ))]
  have hC : (Pcs.map fun _ => Cmax).sum + 7 * 6 ≤ Ctot := by
    have hlenP : Pcs.length = 2 * (pts.length + 1) := by
      simp only [hPcs, List.length_append, List.length_map, laiPieces_length]; ring
    rw [List.map_const', List.sum_replicate, nsmul_eq_mul, hlenP]
    have h1 : ((2 * (pts.length + 1) : ℕ) : ℝ) ≤ 2 * ((K : ℝ) + 1) := by
      push_cast
      have : (pts.length : ℝ) ≤ K := by exact_mod_cast hlen
      linarith
    have := mul_le_mul_of_nonneg_right h1 hCmax0
    rw [hCtot]; nlinarith
  have hW := lai_hW_exp σ hn1 (ℓ := ℓ + ε / 12 + ε / 12) (astar := astar) (ρ := ρ) (q := 6)
    (by norm_num) (by linarith) hat α hα' Pcs (fun _ => Cmax) (fun c hc => (hgood c hc).1)
    hCtot0 hC
  have hsf : ∀ c ∈ laiCurves n a b t v pts Complex.I, SigmaFinite c.ν := by
    intro c hc
    rw [hcs] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
        show SigmaFinite p.nu; infer_instance
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
        show SigmaFinite q.nu; infer_instance
    · unfold atomCurves at hc
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      show SigmaFinite (Measure.dirac (0 : ℝ)); infer_instance
  haveI := listMeasure_sigmaFinite _ hsf
  have hint' : ∀ k : ℕ, Integrable (fun x => listW (laiCurves n a b t v pts Complex.I) x *
      listZ (laiCurves n a b t v pts Complex.I) x ^ k)
      (listMeasure (laiCurves n a b t v pts Complex.I)) := by
    intro k
    refine (integrable_list_iff (laiCurves n a b t v pts Complex.I)
      (fun w z => w * z ^ k)).mpr (fun c hc => ?_)
    rw [hcs] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (hgood c hc).2 k
    · unfold atomCurves at hc
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      show Integrable (fun _ : ℝ => α j * (-(j : ℂ)) ^ k) (Measure.dirac (0 : ℝ))
      exact integrable_const _
  have hint2 : ∀ i j : Fin (3 * n), Integrable (fun x => listW (laiCurves n a b t v pts Complex.I) x *
      listZ (laiCurves n a b t v pts Complex.I) x ^ (i : ℕ) *
      listZ (laiCurves n a b t v pts Complex.I) x ^ (j : ℕ))
      (listMeasure (laiCurves n a b t v pts Complex.I)) := fun i j =>
    (hint' ((i : ℕ) + (j : ℕ))).congr (Filter.Eventually.of_forall fun x => by
      simp only [pow_add]; ring)
  have hT := hR1 (listMeasure (laiCurves n a b t v pts Complex.I))
    (listW (laiCurves n a b t v pts Complex.I)) (listZ (laiCurves n a b t v pts Complex.I))
    (n := n) (M := 3 * n) hnR (by push_cast; ring) hint2 hW.1 hW.2
  have hid := laiJ_eq_det n a b t v hlam hv0 hv2 hvm pts hpts hd (fun i j => hint' _)
  have hprod : 0 < ∏ i ∈ range (3 * n), ((i.factorial : ℝ)) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  have hnorm : |MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n)| =
      laiLam a b ^ (3 * n) * (‖(Matrix.of fun i j : Fin (3 * n) =>
          ∫ x, listW (laiCurves n a b t v pts Complex.I) x *
            listZ (laiCurves n a b t v pts Complex.I) x ^ ((i : ℕ) + (j : ℕ))
            ∂listMeasure (laiCurves n a b t v pts Complex.I)).det‖ /
        ∏ i ∈ range (3 * n), ((i.factorial : ℝ)) ^ 2) := by
    calc _ = ‖((MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
      _ = _ := by
          rw [hid, norm_mul, norm_mul, Complex.norm_real, norm_pow, Complex.norm_real,
            Real.norm_of_nonneg (inv_nonneg.2 hprod.le), Real.norm_of_nonneg hlam.le]
          ring
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left (hT.trans (le_of_eq ?_)) (by positivity)
  congr 1
  ring

/-! ### 4. `W_σ` through the analytic form `Wan` -/

/-- The analytic form of the wedge field on the two segments of Lai's design:
`κ + Re Ψ̃ - 2 U₁ - 2 U₂` (the output of the cell theorems). -/
noncomputable def Wan (c : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℝ :=
  vAnal 3 2 2 6 (2 * Real.pi) s + (-2) * logPotC (segMeasure laiM laiH c N) s +
    (-2) * logPotC (segMeasure (starRingEnd ℂ laiM) (starRingEnd ℂ laiH) c N) s

theorem logPotC_sig2 {M h : ℂ} {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (sig2 M h c N)]
    {bb A α : ℝ} (hσ : BallMajA (sig2 M h c N) bb A α) (s : ℂ) :
    logPotC (sig2 M h c N) s = logPotC (segMeasure M h c N) s +
      logPotC (segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) s := by
  have hi := integrable_log_norm_sub hσ s
  have hi' : Integrable (fun u => Real.log ‖s - u‖)
      (segMeasure M h c N + segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N) := hi
  obtain ⟨h1, h2⟩ := integrable_add_measure.mp hi'
  unfold logPotC
  show -(∫ u, Real.log ‖s - u‖ ∂(segMeasure M h c N +
    segMeasure (starRingEnd ℂ M) (starRingEnd ℂ h) c N)) = _
  rw [integral_add_measure h1 h2]
  ring

theorem Wan_eq {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] {bb A α : ℝ}
    (hσ : BallMajA (laiSigma c N) bb A α) (s : ℂ) :
    Wan c N s = vAnal 3 2 2 6 (2 * Real.pi) s + 2 * potC (laiSigma c N) s := by
  have h1 := logPotC_sig2 hσ s
  have h2 : logPotC (sig2 laiM laiH c N) s = -potC (laiSigma c N) s := rfl
  unfold Wan
  linarith [h1, h2]

theorem wField_eq_Wan {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] {bb A α : ℝ}
    (hσ : BallMajA (laiSigma c N) bb A α) {s : ℂ} (hs : 0 < s.im) :
    wField 3 2 2 6 (2 * Real.pi) (laiSigma c N) s = Wan c N s := by
  rw [wField_eq_potC, ← vAnal_eq_vField 3 2 2 6 (2 * Real.pi) hs, Wan_eq hσ]

/-- **The vertex.**  `W_σ ≤ ℓ + η` on the upper half plane near a point `x₀` of `(0, 2)` where
the analytic form is `≤ ℓ`. -/
theorem near_vertex {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] {bb A : ℝ}
    (hσ : BallMajA (laiSigma c N) bb A (1 / 2)) {x0 : ℂ} (hx0 : 0 < x0.re)
    (hx0' : 0 < 2 - x0.re) {ℓ : ℝ} (hv : Wan c N x0 ≤ ℓ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, 0 < s.im → ‖s - x0‖ < δ →
      wField 3 2 2 6 (2 * Real.pi) (laiSigma c N) s ≤ ℓ + η := by
  obtain ⟨δ1, hδ1, h1⟩ := potC_usc_of hσ.b_pos hσ.ae_mem hσ.singleton_zero
    (integrable_log_norm_sub hσ) x0 (show 0 < η / 4 by linarith)
  have hdom : psiDom 2 6 x0 := psiDom_of_re_pos 2 6 hx0 hx0' (by linarith)
  have hca : ContinuousAt (fun s => vAnal 3 2 2 6 (2 * Real.pi) s) x0 := by
    unfold vAnal
    exact continuousAt_const.add (Complex.continuous_re.continuousAt.comp
      (hasDerivAt_psiT 3 2 2 6 (2 * Real.pi) hdom).continuousAt)
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨δ2, hδ2, h2⟩ := hca (η / 4) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs hsd => ?_⟩
  have e1 := h1 s (lt_of_lt_of_le hsd (min_le_left _ _))
  have e2 := h2 (show dist s x0 < δ2 by
    rw [dist_eq_norm]; exact lt_of_lt_of_le hsd (min_le_right _ _))
  rw [Real.dist_eq] at e2
  have e3 := (abs_lt.mp e2).2
  have e4 := Wan_eq hσ x0
  rw [wField_eq_potC, ← vAnal_eq_vField 3 2 2 6 (2 * Real.pi) hs]
  linarith

/-- The chained cell covers of `W_σ` on the arm (`G0`, `A`, `G1`) and the vertical segment
(`R`), as delivered by `cellG_sound`, `cellA_sound`, `cellR_sound`. -/
structure LaiCover (c : ℕ → ℝ) (N : ℕ) (ℓ wA wB : ℝ) : Prop where
  hwA0 : 0 ≤ wA
  hwB0 : 0 ≤ wB
  hwA : 97 / 93 ≤ Real.cosh wA
  hwB : 103 / 93 ≤ Real.cosh wB
  A : ∀ θ ∈ Icc (0 : ℝ) Real.pi, Wan c N (laiM + laiH * ((Real.cos θ : ℝ) : ℂ)) ≤ ℓ
  G0 : ∀ w ∈ Icc (0 : ℝ) wA, Wan c N (laiM + laiH * (((-1 : ℝ) * Real.cosh w : ℝ) : ℂ)) ≤ ℓ
  G1 : ∀ w ∈ Icc (0 : ℝ) wB, Wan c N (laiM + laiH * (((1 : ℝ) * Real.cosh w : ℝ) : ℂ)) ≤ ℓ
  R : ∀ y ∈ Icc (0 : ℝ) (11 / 10), Wan c N (laiP + Complex.I * (y : ℂ)) ≤ ℓ

theorem arm_param (τ : ℝ) :
    laiX0 + (τ : ℂ) * (laiP - laiX0) = laiM + laiH * (((200 * τ - 97) / 93 : ℝ) : ℂ) := by
  apply Complex.ext
  · csimp
    ring
  · csimp
    ring

theorem arm_cover {c : ℕ → ℝ} {N : ℕ} {ℓ wA wB : ℝ} (hc : LaiCover c N ℓ wA wB) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : Wan c N (laiX0 + (τ : ℂ) * (laiP - laiX0)) ≤ ℓ := by
  rw [arm_param τ]
  have hX1 : -(97 / 93) ≤ (200 * τ - 97) / 93 := by linarith
  have hX2 : (200 * τ - 97) / 93 ≤ 103 / 93 := by linarith
  by_cases h1 : (200 * τ - 97) / 93 < -1
  · obtain ⟨w, hw0, hw⟩ := Real.cosh_surjOn
      (show -((200 * τ - 97) / 93) ∈ Ici (1 : ℝ) from by simp only [Set.mem_Ici]; linarith)
    have hw0' : 0 ≤ w := hw0
    have hwle : w ≤ wA := by
      have : Real.cosh w ≤ Real.cosh wA := by rw [hw]; linarith [hc.hwA]
      rw [Real.cosh_le_cosh, abs_of_nonneg hw0', abs_of_nonneg hc.hwA0] at this
      exact this
    have key := hc.G0 w ⟨hw0', hwle⟩
    have e : (((-1 : ℝ) * Real.cosh w : ℝ) : ℂ) = (((200 * τ - 97) / 93 : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    rw [e] at key
    exact key
  by_cases h2 : 1 < (200 * τ - 97) / 93
  · obtain ⟨w, hw0, hw⟩ := Real.cosh_surjOn
      (show (200 * τ - 97) / 93 ∈ Ici (1 : ℝ) from by simp only [Set.mem_Ici]; linarith)
    have hw0' : 0 ≤ w := hw0
    have hwle : w ≤ wB := by
      have : Real.cosh w ≤ Real.cosh wB := by rw [hw]; linarith [hc.hwB]
      rw [Real.cosh_le_cosh, abs_of_nonneg hw0', abs_of_nonneg hc.hwB0] at this
      exact this
    have key := hc.G1 w ⟨hw0', hwle⟩
    have e : (((1 : ℝ) * Real.cosh w : ℝ) : ℂ) = (((200 * τ - 97) / 93 : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    rw [e] at key
    exact key
  · push_neg at h1 h2
    have key := hc.A (Real.arccos ((200 * τ - 97) / 93))
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    rwa [Real.cos_arccos h1 h2] at key

theorem wField_arm {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] {bb A α : ℝ}
    (hσ : BallMajA (laiSigma c N) bb A α) {ℓ wA wB : ℝ} (hc : LaiCover c N ℓ wA wB) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    wField 3 2 2 6 (2 * Real.pi) (laiSigma c N) (laiX0 + (τ : ℂ) * (laiP - laiX0)) ≤ ℓ := by
  have him : 0 < (laiX0 + (τ : ℂ) * (laiP - laiX0)).im := by
    csimp
    nlinarith [hτ0]
  rw [wField_eq_Wan hσ him]
  exact arm_cover hc hτ0.le hτ1

theorem wField_ray {c : ℕ → ℝ} {N : ℕ} [IsFiniteMeasure (laiSigma c N)] {bb A α : ℝ}
    (hσ : BallMajA (laiSigma c N) bb A α) {ℓ wA wB : ℝ} (hc : LaiCover c N ℓ wA wB) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) (11 / 10)) :
    wField 3 2 2 6 (2 * Real.pi) (laiSigma c N) (laiP + Complex.I * (y : ℂ)) ≤ ℓ := by
  have him : 0 < (laiP + Complex.I * (y : ℂ)).im := by
    csimp
    nlinarith [hy.1]
  rw [wField_eq_Wan hσ him]
  exact hc.R y hy

/-! ### 5. Segments of the polygon -/

theorem norm_seg_lt {s₁ s₂ : ℂ} {R : ℝ} (h1 : ‖s₁‖ < R) (h2 : ‖s₂‖ < R) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : ‖s₁ + (t : ℂ) * (s₂ - s₁)‖ < R := by
  have e : s₁ + (t : ℂ) * (s₂ - s₁) = ((1 - t : ℝ) : ℂ) * s₁ + (t : ℂ) * s₂ := by
    push_cast; ring
  rw [e]
  have h3 : 0 ≤ 1 - t := by linarith [ht.2]
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * s₁‖ + ‖(t : ℂ) * s₂‖ := norm_add_le _ _
    _ = (1 - t) * ‖s₁‖ + t * ‖s₂‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg h3, abs_of_nonneg ht.1.le]
    _ < R := by
        have := mul_le_mul_of_nonneg_left h1.le h3
        have := mul_lt_mul_of_pos_left h2 ht.1
        nlinarith

theorem norm_seg_le {s₁ s₂ : ℂ} {R : ℝ} (h1 : ‖s₁‖ ≤ R) (h2 : ‖s₂‖ ≤ R) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : ‖s₁ + (t : ℂ) * (s₂ - s₁)‖ ≤ R := by
  have e : s₁ + (t : ℂ) * (s₂ - s₁) = ((1 - t : ℝ) : ℂ) * s₁ + (t : ℂ) * s₂ := by
    push_cast; ring
  rw [e]
  have h3 : 0 ≤ 1 - t := by linarith [ht.2]
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * s₁‖ + ‖(t : ℂ) * s₂‖ := norm_add_le _ _
    _ = (1 - t) * ‖s₁‖ + t * ‖s₂‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg h3, abs_of_nonneg ht.1.le]
    _ ≤ R := by
        have := mul_le_mul_of_nonneg_left h1 h3
        have := mul_le_mul_of_nonneg_left h2 ht.1.le
        nlinarith

theorem wField_ball_seg {σ : Measure ℂ} {x0 : ℂ} {δ ℓ' : ℝ}
    (hnear : ∀ s : ℂ, 0 < s.im → ‖s - x0‖ < δ →
      wField 3 2 2 6 (2 * Real.pi) σ s ≤ ℓ')
    {s₁ s₂ : ℂ} (h1 : ‖s₁ - x0‖ < δ) (h2 : ‖s₂ - x0‖ < δ) (hi1 : 0 ≤ s₁.im) (hi2 : 0 < s₂.im)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    wField 3 2 2 6 (2 * Real.pi) σ (s₁ + (t : ℂ) * (s₂ - s₁)) ≤ ℓ' := by
  apply hnear
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.sub_re]
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hi1, mul_pos ht.1 hi2]
  · have e : s₁ + (t : ℂ) * (s₂ - s₁) - x0 =
        (s₁ - x0) + (t : ℂ) * ((s₂ - x0) - (s₁ - x0)) := by ring
    rw [e]
    exact norm_seg_lt h1 h2 ht

theorem zeta_div (a b : ℂ) (n : ℕ) (t : ℝ) :
    (Piece.zeta ⟨a, b - a, false⟩ t) / (n : ℂ) = a / n + (t : ℂ) * (b / n - a / n) := by
  show (a + (t : ℂ) * (b - a)) / (n : ℂ) = _
  ring

theorem pieceOK_mk {σ : Measure ℂ} {n : ℕ} {ℓ' Rs : ℝ} (a b : ℂ)
    (hG : ∀ t ∈ Ioc (0 : ℝ) 1, GoodPt (a + (t : ℂ) * (b - a)))
    (hW : ∀ t ∈ Ioc (0 : ℝ) 1,
      wField 3 2 2 6 (2 * Real.pi) σ (a / n + (t : ℂ) * (b / n - a / n)) ≤ ℓ')
    (hR : ∀ t ∈ Ioc (0 : ℝ) 1, ‖a / n + (t : ℂ) * (b / n - a / n)‖ ≤ Rs) :
    PieceOK σ n ℓ' Rs ⟨a, b - a, false⟩ := by
  intro t ht
  refine ⟨hG t ht, ?_, ?_⟩
  · rw [zeta_div a b n t]; exact hW t ht
  · rw [zeta_div a b n t]; exact hR t ht

theorem pieceGoodS_seg {σ : Measure ℂ} {n : ℕ} {ℓ' Cfin Rs : ℝ} (a b : ℂ)
    (hOK : PieceOK σ n ℓ' Rs ⟨a, b - a, false⟩)
    (hD : ‖b - a‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 ≤
      (n : ℝ) * Cfin) :
    PieceGoodS σ n ℓ' Cfin ⟨a, b - a, false⟩ :=
  ⟨fun _ => ⟨Rs, hOK, hD⟩, fun h => absurd h (by simp)⟩

theorem seg_const_le {D : ℂ} {n : ℕ} (hD : ‖D‖ ≤ 8 * n) :
    ‖D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + 4) ^ 3 ≤
      (n : ℝ) * (8 * ((2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * 5 ^ 3)) := by
  have hK : 0 ≤ (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 (by positivity)) laiKC_nonneg) (Real.exp_pos _).le
  calc _ = ‖D‖ * ((2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * 5 ^ 3) := by ring
    _ ≤ (8 * n) * ((2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * 5 ^ 3) :=
        mul_le_mul_of_nonneg_right hD (mul_nonneg hK (by norm_num))
    _ = _ := by ring

theorem goodPt_of_im_ge {z : ℂ} (hre : 0 ≤ z.re) (him : 1 ≤ z.im) : GoodPt z := by
  have h0 : (0 : ℝ) ≤ z.im := by linarith
  refine ⟨(by linarith : (0 : ℝ) < z.im).ne', hre, ?_, Or.inl ?_⟩
  · have := Complex.abs_im_le_norm z
    rw [abs_of_nonneg h0] at this
    linarith
  · rw [abs_of_nonneg h0]
    exact him

theorem div_sub_eq' (z x : ℂ) {n : ℕ} (hnC : (n : ℂ) ≠ 0) : z / n - x = (z - n * x) / n := by
  first
    | (field_simp; ring)
    | field_simp

/-- The endpoints of the first two pieces are within `δ` of the vertex. -/
theorem near_x0 {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hnδ : 3 ≤ (n : ℝ) * δ) {v : ℝ}
    (hv : |v - 8 / 5 * n| ≤ 1 / 2) :
    ‖(v : ℂ) / n - laiX0‖ < δ ∧ ‖((v : ℂ) + Complex.I) / n - laiX0‖ < δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hv' := abs_le.mp hv
  have hx1 : 0 ≤ v - 8 / 5 * n + 1 / 2 := by linarith [hv'.1]
  have hx2 : 0 ≤ 1 / 2 - (v - 8 / 5 * n) := by linarith [hv'.2]
  have e1 := div_sub_eq' (v : ℂ) laiX0 hnC
  have e2 := div_sub_eq' ((v : ℂ) + Complex.I) laiX0 hnC
  have b1 : ‖(v : ℂ) - n * laiX0‖ ≤ 1 / 2 := by
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    nlinarith [mul_nonneg hx1 hx2]
  have b2 : ‖(v : ℂ) + Complex.I - n * laiX0‖ ≤ 3 / 2 := by
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    nlinarith [mul_nonneg hx1 hx2]
  rw [e1, e2, norm_div, norm_div, Complex.norm_natCast, div_lt_iff₀ hn0, div_lt_iff₀ hn0]
  constructor <;> nlinarith

/-- The point `q = x₀ + τ (P - x₀)`, close to the vertex. -/
theorem norm_q_sub {τ : ℝ} (hτ0 : 0 ≤ τ) :
    ‖laiX0 + (τ : ℂ) * (laiP - laiX0) - laiX0‖ ≤ 3 * τ := by
  have e : laiX0 + (τ : ℂ) * (laiP - laiX0) - laiX0 = (τ : ℂ) * (laiP - laiX0) := by ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
  have h3 : ‖laiP - laiX0‖ ≤ 3 := by
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    norm_num
  calc τ * ‖laiP - laiX0‖ ≤ τ * 3 := mul_le_mul_of_nonneg_left h3 hτ0
    _ = 3 * τ := by ring

/-! ### 6. The polygon and `hcont` -/

set_option maxHeartbeats 3200000 in
theorem lai_hcont {c : ℕ → ℝ} {N : ℕ} {wA wB : ℝ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (hc0 : c 0 = 3 / 2)
    (hcov : LaiCover c N laiEll wA wB) :
    ∀ η : ℝ, 0 < η → ∃ (N₀ K : ℕ) (Cfin : ℝ), ∀ n : ℕ, N₀ ≤ n → ∃ (v : ℝ) (pts : List ℂ),
      0 < v ∧ v < 2 * n + 1 ∧ (∀ m : ℤ, v ≠ m) ∧ (∀ z ∈ pts, 0 < z.im) ∧ pts.length ≤ K ∧
      ∀ p ∈ laiPieces v pts Complex.I, PieceGoodS (laiSigma c N) n (laiEll + η) Cfin p := by
  intro η hη
  haveI := isFiniteMeasure_sig2 (M := laiM) (h := laiH) hpos
  have hσ := ballMajA_sig2 (M := laiM) laiH_ne c N
  have hmass : (laiSigma c N).real univ = 3 := by
    show (sig2 laiM laiH c N).real univ = 3
    rw [sig2_real_univ hpos (by rw [hc0]; norm_num), hc0]
    norm_num
  have hv : Wan c N laiX0 ≤ laiEll := by
    have := arm_cover hcov (τ := 0) le_rfl zero_le_one
    simpa using this
  obtain ⟨δ, hδ, hnear⟩ := near_vertex hσ (x0 := laiX0) (by norm_num [laiX0_re])
    (by norm_num [laiX0_re]) hv hη
  have hτ0 : 0 < min (1 / 50 : ℝ) (δ / 12) := lt_min (by norm_num) (by linarith)
  have hτ1 : min (1 / 50 : ℝ) (δ / 12) ≤ 1 / 50 := min_le_left _ _
  have hτ2 : min (1 / 50 : ℝ) (δ / 12) ≤ δ / 12 := min_le_right _ _
  generalize min (1 / 50 : ℝ) (δ / 12) = τ at hτ0 hτ1 hτ2
  refine ⟨⌈3 / δ + 5 / τ⌉₊ + 2, 4,
    8 * ((2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * 5 ^ 3), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hnreal : 3 / δ + 5 / τ ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (3 / δ + 5 / τ)
    have h2 : ((⌈3 / δ + 5 / τ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : ⌈3 / δ + 5 / τ⌉₊ ≤ n)
    linarith
  have hnδ : 3 ≤ (n : ℝ) * δ := by
    have : 3 / δ ≤ (n : ℝ) := by
      have : 0 ≤ 5 / τ := div_nonneg (by norm_num) hτ0.le
      linarith
    rwa [div_le_iff₀ hδ] at this
  have hnτ : 5 ≤ (n : ℝ) * τ := by
    have : 5 / τ ≤ (n : ℝ) := by
      have : 0 ≤ 3 / δ := div_nonneg (by norm_num) hδ.le
      linarith
    rwa [div_le_iff₀ hτ0] at this
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  -- the real crossing point
  have hfl1 : (⌊(8 / 5 : ℝ) * n⌋ : ℝ) ≤ 8 / 5 * n := Int.floor_le _
  have hfl2 : 8 / 5 * (n : ℝ) < (⌊(8 / 5 : ℝ) * n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hfl0' : (0 : ℤ) ≤ ⌊(8 / 5 : ℝ) * n⌋ := Int.floor_nonneg.mpr (by positivity)
  have hfl0 : (0 : ℝ) ≤ (⌊(8 / 5 : ℝ) * n⌋ : ℝ) := by exact_mod_cast hfl0'
  generalize hvdef : (⌊(8 / 5 : ℝ) * n⌋ : ℝ) + 1 / 2 = v
  have hvd : |v - 8 / 5 * n| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hv0 : 1 / 2 ≤ v := by linarith
  have hvle : v ≤ 8 / 5 * n + 1 / 2 := by linarith
  -- the point q on the arm
  set q : ℂ := laiX0 + (τ : ℂ) * (laiP - laiX0) with hq
  have hq_re : q.re = 8 / 5 + τ / 2 := by
    rw [hq]; csimp; ring
  have hq_im : q.im = τ * (11 / 5) := by
    rw [hq]; csimp; ring
  have hqn : ‖q‖ ≤ 4 := by
    refine norm_le_of_coords (by norm_num) ?_
    rw [hq_re, hq_im]
    nlinarith
  have hqx : ‖q - laiX0‖ < δ := by
    have := norm_q_sub (τ := τ) hτ0.le
    rw [← hq] at this
    linarith
  have hPn : ‖laiP‖ ≤ 4 := by
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    norm_num
  have hTn : ‖laiT‖ ≤ 4 := by
    refine norm_le_of_coords (by norm_num) ?_
    csimp
    norm_num
  have hnq : 1 ≤ (n : ℝ) * (τ * (11 / 5)) := by linarith
  obtain ⟨hs0, hs1⟩ := near_x0 hn1 hnδ hvd
  have hvn : ‖(v : ℂ) / n‖ ≤ 4 := by
    have e : ‖(v : ℂ) / n‖ = v / n := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ v by linarith)]
    rw [e, div_le_iff₀ hn0]
    linarith
  have hv1n : ‖((v : ℂ) + Complex.I) / n‖ ≤ 4 := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn0]
    calc ‖(v : ℂ) + Complex.I‖ ≤ ‖(v : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = v + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ v by linarith),
            Complex.norm_I]
      _ ≤ 4 * n := by linarith
  have him_vI : (((v : ℂ) + Complex.I) / n).im = 1 / n := by
    rw [Complex.div_natCast_im]; simp
  have him_v : ((v : ℂ) / n).im = 0 := by
    rw [Complex.div_natCast_im]; simp
  have him_nq : ((n : ℂ) * q).im = n * (τ * (11 / 5)) := by
    csimp; rw [hq_im]; ring
  have him_nP : ((n : ℂ) * laiP).im = n * (11 / 5) := by
    csimp; ring
  have him_nT : ((n : ℂ) * laiT).im = n * (33 / 10) := by
    csimp; ring
  refine ⟨v, [(v : ℂ) + Complex.I, (n : ℂ) * q, (n : ℂ) * laiP, (n : ℂ) * laiT], by linarith,
    by linarith, ?_, ?_, by simp, ?_⟩
  · intro m hm
    have h1 : ((m - ⌊(8 / 5 : ℝ) * n⌋ : ℤ) : ℝ) = 1 / 2 := by
      push_cast
      linarith
    have h2 : (0 : ℤ) < m - ⌊(8 / 5 : ℝ) * n⌋ := by
      have : (0 : ℝ) < ((m - ⌊(8 / 5 : ℝ) * n⌋ : ℤ) : ℝ) := by rw [h1]; norm_num
      exact_mod_cast this
    have h3 : m - ⌊(8 / 5 : ℝ) * n⌋ < (1 : ℤ) := by
      have : ((m - ⌊(8 / 5 : ℝ) * n⌋ : ℤ) : ℝ) < 1 := by rw [h1]; norm_num
      exact_mod_cast this
    omega
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · csimp; norm_num
    · rw [him_nq]; exact mul_pos hn0 (mul_pos hτ0 (by norm_num))
    · rw [him_nP]; exact mul_pos hn0 (by norm_num)
    · rw [him_nT]; exact mul_pos hn0 (by norm_num)
  · intro p hp
    have hpl : laiPieces v [(v : ℂ) + Complex.I, (n : ℂ) * q, (n : ℂ) * laiP, (n : ℂ) * laiT]
        Complex.I =
        [⟨(v : ℂ), ((v : ℂ) + Complex.I) - (v : ℂ), false⟩,
         ⟨(v : ℂ) + Complex.I, (n : ℂ) * q - ((v : ℂ) + Complex.I), false⟩,
         ⟨(n : ℂ) * q, (n : ℂ) * laiP - (n : ℂ) * q, false⟩,
         ⟨(n : ℂ) * laiP, (n : ℂ) * laiT - (n : ℂ) * laiP, false⟩,
         ⟨(n : ℂ) * laiT, Complex.I, true⟩] := by
      first
        | rfl
        | simp [laiPieces, polyPieces, chainPieces]
    rw [hpl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · -- piece 1: v → v + i
      refine pieceGoodS_seg (Rs := 4) _ _ ?_ ?_
      · refine pieceOK_mk _ _ ?_ ?_ ?_
        · intro t ht
          have eim : ((v : ℂ) + (t : ℂ) * ((v : ℂ) + Complex.I - (v : ℂ))).im = t := by
            csimp; ring
          have ere : ((v : ℂ) + (t : ℂ) * ((v : ℂ) + Complex.I - (v : ℂ))).re = v := by
            csimp; ring
          refine ⟨?_, ?_, ?_, Or.inr ⟨⌊(8 / 5 : ℝ) * n⌋, ?_⟩⟩
          · rw [eim]; exact ht.1.ne'
          · rw [ere]; linarith
          · have := Complex.abs_re_le_norm ((v : ℂ) + (t : ℂ) * ((v : ℂ) + Complex.I - (v : ℂ)))
            rw [ere, abs_of_nonneg (show (0 : ℝ) ≤ v by linarith)] at this
            linarith
          · rw [ere, ← hvdef]
            ring
        · intro t ht
          exact wField_ball_seg hnear hs0 hs1 (le_of_eq him_v.symm)
            (by rw [him_vI]; exact one_div_pos.mpr hn0) ht
        · intro t ht
          exact norm_seg_le hvn hv1n ht
      · apply seg_const_le
        have : ‖(v : ℂ) + Complex.I - (v : ℂ)‖ = 1 := by simp
        rw [this]
        exact le_trans (by norm_num) (mul_le_mul_of_nonneg_left hn2r (by norm_num : (0 : ℝ) ≤ 8))
    · -- piece 2: v + i → n q
      refine pieceGoodS_seg (Rs := 4) _ _ ?_ ?_
      · refine pieceOK_mk _ _ ?_ ?_ ?_
        · intro t ht
          have h1 : 0 ≤ (1 - t) * v := mul_nonneg (by linarith [ht.2]) (by linarith)
          have h2 : 0 ≤ t * ((n : ℝ) * (8 / 5 + τ / 2)) :=
            mul_nonneg ht.1.le (mul_nonneg hn0.le (by linarith))
          have h3 : 0 ≤ t * ((n : ℝ) * (τ * (11 / 5)) - 1) :=
            mul_nonneg ht.1.le (by linarith)
          apply goodPt_of_im_ge
          · csimp
            rw [hq_re]
            linarith
          · csimp
            rw [hq_im]
            linarith
        · intro t ht
          have e : (n : ℂ) * q / n = q := mul_div_cancel_left₀ _ hnC
          rw [e]
          exact wField_ball_seg hnear hs1 hqx (by rw [him_vI]; exact (one_div_pos.mpr hn0).le)
            (by rw [hq_im]; exact mul_pos hτ0 (by norm_num)) ht
        · intro t ht
          have e : (n : ℂ) * q / n = q := mul_div_cancel_left₀ _ hnC
          rw [e]
          exact norm_seg_le hv1n hqn ht
      · apply seg_const_le
        have h1 : ‖(n : ℂ) * q - ((v : ℂ) + Complex.I)‖ ≤ ‖(n : ℂ) * q‖ + ‖(v : ℂ) + Complex.I‖ :=
          norm_sub_le _ _
        have h2 : ‖(n : ℂ) * q‖ ≤ 4 * n := by
          rw [norm_mul, Complex.norm_natCast]
          linarith [mul_nonneg hn0.le (sub_nonneg.2 hqn)]
        have h3 : ‖(v : ℂ) + Complex.I‖ ≤ 4 * n := by
          have := hv1n
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn0] at this
          linarith
        linarith
    · -- piece 3: n q → n P (on the arm)
      refine pieceGoodS_seg (Rs := 4) _ _ ?_ ?_
      · refine pieceOK_mk _ _ ?_ ?_ ?_
        · intro t ht
          have h1 : 0 ≤ (1 - t) * ((n : ℝ) * (8 / 5 + τ / 2)) :=
            mul_nonneg (by linarith [ht.2]) (mul_nonneg hn0.le (by linarith))
          have h2 : 0 ≤ t * ((n : ℝ) * (21 / 10)) := mul_nonneg ht.1.le (by linarith)
          have h3 : 0 ≤ (1 - t) * ((n : ℝ) * (τ * (11 / 5)) - 1) :=
            mul_nonneg (by linarith [ht.2]) (by linarith)
          have h4 : 0 ≤ t * ((n : ℝ) * (11 / 5) - 1) := mul_nonneg ht.1.le (by linarith)
          apply goodPt_of_im_ge
          · csimp
            rw [hq_re]
            linarith
          · csimp
            rw [hq_im]
            linarith
        · intro t ht
          have e1 : (n : ℂ) * q / n = q := mul_div_cancel_left₀ _ hnC
          have e2 : (n : ℂ) * laiP / n = laiP := mul_div_cancel_left₀ _ hnC
          rw [e1, e2]
          have e : q + (t : ℂ) * (laiP - q) =
              laiX0 + ((τ + t * (1 - τ) : ℝ) : ℂ) * (laiP - laiX0) := by
            rw [hq]; push_cast; ring
          rw [e]
          have hp1 := mul_nonneg ht.1.le (sub_nonneg.2 (by linarith : τ ≤ 1))
          have hp2 := mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 (by linarith : τ ≤ 1))
          have := wField_arm hσ hcov (τ := τ + t * (1 - τ)) (by linarith) (by linarith)
          linarith
        · intro t ht
          have e1 : (n : ℂ) * q / n = q := mul_div_cancel_left₀ _ hnC
          have e2 : (n : ℂ) * laiP / n = laiP := mul_div_cancel_left₀ _ hnC
          rw [e1, e2]
          exact norm_seg_le hqn hPn ht
      · apply seg_const_le
        have e : (n : ℂ) * laiP - (n : ℂ) * q = (n : ℂ) * (laiP - q) := by ring
        rw [e, norm_mul, Complex.norm_natCast]
        have : ‖laiP - q‖ ≤ 8 := by
          calc ‖laiP - q‖ ≤ ‖laiP‖ + ‖q‖ := norm_sub_le _ _
            _ ≤ 8 := by linarith
        linarith [mul_nonneg hn0.le (sub_nonneg.2 this)]
    · -- piece 4: n P → n T (the vertical segment)
      refine pieceGoodS_seg (Rs := 4) _ _ ?_ ?_
      · refine pieceOK_mk _ _ ?_ ?_ ?_
        · intro t ht
          have h1 : 0 ≤ t * ((n : ℝ) * (11 / 10)) := mul_nonneg ht.1.le (by linarith)
          apply goodPt_of_im_ge
          · csimp
            linarith
          · csimp
            linarith
        · intro t ht
          have e1 : (n : ℂ) * laiP / n = laiP := mul_div_cancel_left₀ _ hnC
          have e2 : (n : ℂ) * laiT / n = laiT := mul_div_cancel_left₀ _ hnC
          rw [e1, e2]
          have e : laiP + (t : ℂ) * (laiT - laiP) =
              laiP + Complex.I * ((11 / 10 * t : ℝ) : ℂ) := by
            apply Complex.ext <;> csimp <;> ring
          rw [e]
          have := wField_ray hσ hcov (y := 11 / 10 * t)
            ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
          linarith
        · intro t ht
          have e1 : (n : ℂ) * laiP / n = laiP := mul_div_cancel_left₀ _ hnC
          have e2 : (n : ℂ) * laiT / n = laiT := mul_div_cancel_left₀ _ hnC
          rw [e1, e2]
          exact norm_seg_le hPn hTn ht
      · apply seg_const_le
        have e : (n : ℂ) * laiT - (n : ℂ) * laiP = (n : ℂ) * (laiT - laiP) := by ring
        rw [e, norm_mul, Complex.norm_natCast]
        have : ‖laiT - laiP‖ ≤ 8 := by
          calc ‖laiT - laiP‖ ≤ ‖laiT‖ + ‖laiP‖ := norm_sub_le _ _
            _ ≤ 8 := by linarith
        linarith [mul_nonneg hn0.le (sub_nonneg.2 this)]
    · -- the ray from n T
      refine ⟨fun h => absurd h (by simp), fun _ => ⟨by simp, ?_⟩⟩
      have key := lai_rayOK (laiSigma c N) hmass (laiSigma_disc_ae c N)
        (fun y _ => integrable_log_norm_sub hσ _) hn1
        (p := ⟨(n : ℂ) * laiT, Complex.I, true⟩) rfl rfl
        (by
          show (n : ℂ) * laiT = (n : ℂ) * (((21 / 10 : ℝ) : ℂ) + ((33 / 10 : ℝ) : ℂ) * Complex.I)
          congr 1
          apply Complex.ext <;> csimp <;> ring)
      exact key.mono_ell (by show (-130471 / 10000 : ℝ) ≤ -130471 / 10000 + η; linarith)

/-! ### 7. LD10: the decay bound -/

/-- **LD10.**  Theorem A for Lai's family at the two-arcsine-segment measure.  Hypotheses:
`f = Σ c_k T_k ≥ 0` with `c₀ = 3/2` (the SOS identity of LD21), the chained cell covers
(`LaiCover`, the 40 cell checks of LD19), and the two atom numbers `a(x*)`, `a'(x*)`.
Conclusion: for every `ε > 0` there is `R₀` such that for all `n ≥ R₀`, all `(a, b)` with
`λ = 3|a| + |b| > 0` and all `|t| ≤ λ e^{-ρ n}`,
`|J_n(a, b, aζ(3) + bζ(4) + t)| ≤ λ^{3n} exp(-(D - ε) n²)`, `D = -(κ - energyC σ + 3 ℓ)`. -/
theorem lai_decay_instance {c : ℕ → ℝ} {N : ℕ} {wA wB a0 AA ρ : ℝ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (hc0 : c 0 = 3 / 2)
    (hcov : LaiCover c N laiEll wA wB)
    (ha0 : omegaF 3 2 2 6 (2211 / 500) +
      2 * ∫ u, Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖ ∂(laiSigma c N) ≤ a0)
    (hA : |omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂(laiSigma c N)| ≤ AA)
    (hρ : a0 + AA ^ 2 / (2 * (49 / 100)) ≤ laiEll + ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ n : ℕ, R₀ ≤ n → ∀ a b t : ℝ, 0 < laiLam a b →
      |t| ≤ laiLam a b * Real.exp (-(ρ * n)) →
      |MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n)| ≤
        laiLam a b ^ (3 * n) * Real.exp (-(-((3 : ℝ) ^ 2 * (3 / 2 - Real.log 3) -
          energyC (laiSigma c N) + 3 * laiEll) - ε) * (n : ℝ) ^ 2) := by
  haveI := isFiniteMeasure_sig2 (M := laiM) (h := laiH) hpos
  have hσ := ballMajA_sig2 (M := laiM) laiH_ne c N
  have hmass : (laiSigma c N).real univ = 3 := by
    show (sig2 laiM laiH c N).real univ = 3
    rw [sig2_real_univ hpos (by rw [hc0]; norm_num), hc0]
    norm_num
  have hat := CatalanCore.Lai.DecayTail.lai_atom_bound (σ := laiSigma c N) hmass (laiSigma_re_ae c N)
    (laiSigma_hint hσ) laiSigma_hint1 ha0 hA
  exact lai_decay_dual_S hσ hmass (sig2_conj laiM laiH c N) hρ hat (lai_hcont hpos hc0 hcov)

end CatalanCore.Lai.DecayInstance

open CatalanCore.Lai.DecayInstance in
#print axioms lai_decay_instance
