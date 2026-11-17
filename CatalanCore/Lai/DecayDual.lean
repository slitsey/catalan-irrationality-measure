module

public import CatalanCore.Decay.CurveFamily
public import CatalanCore.Decay.WedgeBounds
public import CatalanCore.Decay.LemmaW
public import CatalanCore.Decay.TheoremA
public import CatalanCore.Lai.DecayContour
public import CatalanCore.Lai.DecayTail

@[expose] public section

/-!
# Lai decay, Theorem A in dual form (LD09): `lai_decay_dual`

* `rhoT_pt_le`: Lemma W with the dual potential at a good point.
* `wField_usc`: upper semicontinuity of `W_σ` off the imaginary axis.
* `PieceOK`, `RayOK`, `curveBd_seg/ray/atom`, `lai_hW_exp`: the weight integral bound.
* `laiCurves`, `laiJ_eq_det`: `J_n(a, b, aζ(3) + bζ(4) + t)` is `λ^{3n}/∏ i!²` times the Hankel
  determinant of the moments of the weighted curve family (contour weight and atoms).
* `lai_decay_dual`: `|J_n| ≤ λ^{3n} exp(-(D - ε) n²)` for `|t| ≤ λ e^{-ρ n}`, uniformly in the direction.

Say μ, never B, for the irrationality measure; `B` below is the design parameter.
-/


open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayDual

open CatalanCore.Lai CatalanCore.Decay.LemmaW CatalanCore.Decay.ComplexContour
  CatalanCore.Lai.DecayContour CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexEnergy
  CatalanCore.Decay.WedgeBounds CatalanCore.Tools.Joukowski
  CatalanCore.Decay.CurveFamily

/-! ### A. `R_n` of Lai's design -/

theorem Rn_eq_lai (n : ℕ) (z : ℂ) :
    Rn 3 2 2 6 n z = aeval z (laiNum n) / (aeval z (laiDen n)) ^ 2 := by
  have hpoch : aeval z (laiPoch n) =
      ∏ i ∈ range (2 * n), (z - (((i + 1 : ℕ) : ℝ) : ℂ)) := by
    unfold laiPoch
    rw [map_prod]
    rw [← Finset.prod_range_reflect (fun i => z - (((i + 1 : ℕ) : ℝ) : ℂ)) (2 * n)]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [map_sub, aeval_X, aeval_C]
    have h1 : ((2 * n - 1 - i + 1 : ℕ) : ℝ) = 2 * n - i := by
      rw [show 2 * n - 1 - i + 1 = 2 * n - i by omega, Nat.cast_sub hi'.le]; push_cast; ring
    rw [h1]
    simp
  have hden : aeval z (laiDen n) = ∏ k ∈ range (6 * n + 1), (z + ((k : ℝ) : ℂ)) := by
    rw [laiDen_eq, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp
  have hnum : aeval z (laiNum n) =
      ((((6 * n).factorial : ℂ)) ^ 2 / (((2 * n).factorial : ℂ)) ^ 3) *
        (∏ i ∈ range (2 * n), (z - (((i + 1 : ℕ) : ℝ) : ℂ))) ^ 3 := by
    unfold laiNum
    rw [map_mul, aeval_C, map_pow, hpoch]
    unfold laiC
    simp
  unfold Rn
  rw [hnum, hden, Finset.prod_pow, ← Finset.prod_pow]
  simp only [Finset.prod_pow]

/-! ### B. The contour integrand is `R_n K_c z^k` -/

theorem laiIntegrand_eq_rho (n k : ℕ) (hk : k < 6 * n) (a b : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    laiIntegrand n (X ^ k) a b z =
      Rn 3 2 2 6 n z * Kc laiJets (laiCoefJ a b) z * z ^ k := by
  have hdeg : (X ^ k : ℚ[X]).degree < ((6 * n : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]; exact_mod_cast hk
  have hpole : ∀ j ∈ range (6 * n + 1), z + (j : ℂ) ≠ 0 := by
    intro j _ h
    apply hz
    have := congrArg Complex.im h
    simpa using this
  unfold laiIntegrand
  rw [ratF_eq_laiR n (X ^ k) hdeg hpole, Rn_eq_lai]
  simp only [map_pow, aeval_X]
  ring

/-! ### C. Measurability -/

theorem measurable_Rn (e r B K n : ℕ) : Measurable (Rn e r B K n) := by
  unfold Rn
  fun_prop

theorem measurable_cotJet_succ (j : ℕ) : Measurable (cotJet (j + 1)) := by
  unfold cotJet
  refine measurable_const.mul ?_
  rw [iteratedDeriv_eq_iterate, Function.iterate_succ']
  exact measurable_deriv _

theorem measurable_Kc (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) (c : ℕ → ℂ) : Measurable (Kc J c) := by
  unfold Kc
  refine Finset.measurable_sum _ fun j hj => ?_
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by have := hJ j hj; omega⟩
  exact measurable_const.mul (measurable_cotJet_succ m)

/-! ### D. The pointwise weight bound -/

/-- The weight `ρ̃_n(z) = R_n(z) K_c(z) / λ`, `λ = 3|a| + |b|`, `c = (-3a, b)`. -/
noncomputable def rhoT (n : ℕ) (a b : ℝ) (z : ℂ) : ℂ :=
  Rn 3 2 2 6 n z * Kc laiJets (laiCoefJ a b) z / (((3 * |a| + |b| : ℝ)) : ℂ)

lemma laiJets_ge : ∀ j ∈ laiJets, 1 ≤ j := by
  intro j hj; unfold laiJets at hj; simp at hj; omega

theorem measurable_rhoT (n : ℕ) (a b : ℝ) : Measurable (rhoT n a b) := by
  unfold rhoT
  exact ((measurable_Rn 3 2 2 6 n).mul (measurable_Kc laiJets laiJets_ge _)).div_const _

/-- The jet constant of Lai's family. -/
noncomputable def laiKC : ℝ := (jetConst 0 + jetConstH 0) + (jetConst 1 + jetConstH 1)

lemma laiKC_nonneg : 0 ≤ laiKC := by
  unfold laiKC
  have := jetConst_nonneg 0; have := jetConst_nonneg 1
  have := jetConstH_nonneg 0; have := jetConstH_nonneg 1
  linarith

lemma kcConst_laiJets_le (a b : ℝ) :
    kcConst laiJets (laiCoefJ a b) ≤ (3 * |a| + |b|) * laiKC := by
  unfold kcConst laiJets laiCoefJ laiKC
  rw [Finset.sum_pair (by norm_num)]
  simp only [if_true, show (2 : ℕ) ≠ 1 from by norm_num, if_false, Nat.add_one_sub_one,
    show (2 : ℕ) - 1 = 1 from rfl, show (1 : ℕ) - 1 = 0 from rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_neg]
  have h1 := jetConst_nonneg 0; have h2 := jetConst_nonneg 1
  have h3 := jetConstH_nonneg 0; have h4 := jetConstH_nonneg 1
  have := abs_nonneg a; have := abs_nonneg b
  norm_num
  nlinarith [mul_nonneg (abs_nonneg a) (add_nonneg h1 h3), mul_nonneg (abs_nonneg b) (add_nonneg h2 h4),
    mul_nonneg (abs_nonneg a) (add_nonneg h2 h4), mul_nonneg (abs_nonneg b) (add_nonneg h1 h3)]

lemma wField_eq_potC (e r B K θ : ℝ) (σ : Measure ℂ) (s : ℂ) :
    wField e r B K θ σ s = CatalanCore.Decay.ComplexTaylor.vField e r B K θ s + 2 * potC σ s := by
  unfold wField logPotC potC
  ring

/-- The conditions under which Lemma W applies to a point of the contour. -/
def GoodPt (z : ℂ) : Prop :=
  z.im ≠ 0 ∧ 0 ≤ z.re ∧ (1 : ℝ) / 2 ≤ ‖z‖ ∧ (1 ≤ |z.im| ∨ ∃ k : ℤ, z.re = (2 * k + 1) / 2)

lemma GoodPt.conj {z : ℂ} (h : GoodPt z) : GoodPt (starRingEnd ℂ z) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, ?_⟩
  simpa using h4

/-- **Pointwise bound** (Lemma W with the dual potential): at a good point `z`,
`‖ρ̃_n z‖ e^{2n potC σ (z/n)} ≤ laiKC · exp (n W_σ(z/n) + C₀ + 4 log n + 3 log (1 + ‖z/n‖))`. -/
theorem rhoT_pt_le (σ : Measure ℂ) (a b : ℝ) (hlam : 0 < 3 * |a| + |b|) (n : ℕ) (hn : 1 ≤ n)
    {z : ℂ} (hz : GoodPt z) :
    ‖rhoT n a b z‖ * Real.exp (2 * n * potC σ (z / n)) ≤
      laiKC * Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (z / (n : ℂ)) + RConst 3 2 2 6 +
        4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) := by
  obtain ⟨him, hre, hz2, hgood⟩ := hz
  have h := norm_RKc_le him hre hz2 hgood laiJets laiJets_ge (laiCoefJ a b) 3 2 2 6 n (by norm_num)
    (by norm_num) hn
  have h' : ‖Rn 3 2 2 6 n z * Kc laiJets (laiCoefJ a b) z‖ ≤ kcConst laiJets (laiCoefJ a b) *
      Real.exp ((n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField 3 2 2 6 (2 * Real.pi) (z / (n : ℂ)) +
        RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) := by
    refine h.trans (le_of_eq ?_)
    congr 2
    push_cast
    ring
  have hkc := kcConst_laiJets_le a b
  have hnorm : ‖rhoT n a b z‖ =
      ‖Rn 3 2 2 6 n z * Kc laiJets (laiCoefJ a b) z‖ / (3 * |a| + |b|) := by
    unfold rhoT
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  have hE : 0 < Real.exp ((n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField 3 2 2 6 (2 * Real.pi) (z / (n : ℂ)) +
        RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) := Real.exp_pos _
  have h1 : ‖rhoT n a b z‖ ≤ laiKC * Real.exp ((n : ℝ) *
      CatalanCore.Decay.ComplexTaylor.vField 3 2 2 6 (2 * Real.pi) (z / (n : ℂ)) +
        RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) := by
    rw [hnorm, div_le_iff₀ hlam]
    calc _ ≤ kcConst laiJets (laiCoefJ a b) * Real.exp ((n : ℝ) *
          CatalanCore.Decay.ComplexTaylor.vField 3 2 2 6 (2 * Real.pi) (z / (n : ℂ)) +
          RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) := h'
      _ ≤ ((3 * |a| + |b|) * laiKC) * Real.exp ((n : ℝ) *
          CatalanCore.Decay.ComplexTaylor.vField 3 2 2 6 (2 * Real.pi) (z / (n : ℂ)) +
          RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) :=
          mul_le_mul_of_nonneg_right hkc hE.le
      _ = _ := by ring
  have key : Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (z / (n : ℂ)) + RConst 3 2 2 6 +
        4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) =
      Real.exp ((n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField 3 2 2 6 (2 * Real.pi) (z / (n : ℂ)) +
        RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖z / (n : ℂ)‖)) *
      Real.exp (2 * n * potC σ (z / n)) := by
    rw [← Real.exp_add, wField_eq_potC]
    congr 1
    ring
  rw [key, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

end CatalanCore.Lai.DecayDual


open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayDual

open CatalanCore.Lai CatalanCore.Decay.LemmaW CatalanCore.Decay.ComplexContour
  CatalanCore.Lai.DecayContour CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexEnergy
  CatalanCore.Decay.WedgeBounds CatalanCore.Tools.Joukowski
  CatalanCore.Decay.CurveFamily

/-! ### E. The potential of Lebesgue measure on `[0, B]` -/

/-- Lebesgue measure on `[0, B] ⊂ ℝ ⊂ ℂ`. -/
noncomputable def lebMeas (B : ℝ) : Measure ℂ :=
  lineDens (fun t : ℝ => (t : ℂ)) (fun _ => (1 : ℝ)) 0 B

theorem ballMaj_lebMeas {B : ℝ} (hB : 0 < B) : BallMaj (lebMeas B) B 4 := by
  have h := ballMaj_lineDens (γ := fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal
    (a := 0) (b := B) (ρ := fun _ => (1 : ℝ)) (F := 1) zero_le_one (fun _ => le_rfl)
    (lam := 1) one_pos
    (fun s t => by simp [← Complex.ofReal_sub, Complex.norm_real]) (b₀ := B) hB
    (fun t ht => by simpa [Complex.norm_real, abs_of_nonneg ht.1] using ht.2)
  simpa [lebMeas] using h

instance lebMeas_finite (B : ℝ) : IsFiniteMeasure (lebMeas B) := by
  refine ⟨?_⟩
  have h := lineDens_apply_le (γ := fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal
    (a := 0) (b := B) (ρ := fun _ => (1 : ℝ)) (F := 1) (fun _ => le_rfl) MeasurableSet.univ
  unfold lebMeas
  refine h.trans_lt ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact (measure_mono (inter_subset_right)).trans_lt (by simp)

theorem potC_lebMeas {B : ℝ} (hB : 0 ≤ B) (s : ℂ) :
    potC (lebMeas B) s = ∫ x in (0 : ℝ)..B, Real.log ‖s - (x : ℂ)‖ := by
  unfold potC lebMeas lineDens
  have hd : (fun t : ℝ => ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) t)) = 1 := by
    funext t; simp
  rw [hd, withDensity_one]
  have hm : Measurable fun u : ℂ => Real.log ‖s - u‖ := Measurable.log (by fun_prop)
  rw [integral_map Complex.measurable_ofReal.aemeasurable hm.aestronglyMeasurable,
    intervalIntegral.integral_of_le hB, ← integral_Icc_eq_integral_Ioc]

/-! ### F. Continuity of the `K`-integral away from `Re = 0` -/

lemma abs_log_le_of_mem {lo hi y : ℝ} (hlo : 0 < lo) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    |Real.log y| ≤ |Real.log lo| + Real.log (1 + hi) := by
  have hy : 0 < y := lt_of_lt_of_le hlo h1
  have hL : 0 ≤ Real.log (1 + hi) := Real.log_nonneg (by linarith)
  rcases le_or_gt 1 y with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have : Real.log y ≤ Real.log (1 + hi) := Real.log_le_log hy (by linarith)
    linarith [abs_nonneg (Real.log lo)]
  · rw [abs_of_neg (Real.log_neg hy h)]
    have : Real.log lo ≤ Real.log y := Real.log_le_log hlo h1
    have := neg_le_abs (Real.log lo)
    linarith

theorem continuousAt_I2 {K : ℝ} (hK : 0 ≤ K) {s0 : ℂ} (hs0 : 0 < s0.re) :
    ContinuousAt (fun s : ℂ => ∫ x in (0 : ℝ)..K, Real.log ‖s + (x : ℂ)‖) s0 := by
  have hr2 : 0 < s0.re / 2 := by positivity
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => |Real.log (s0.re / 2)| + Real.log (1 + (‖s0‖ + s0.re / 2 + K))) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun s => ?_
    have : Measurable fun x : ℝ => Real.log ‖s + (x : ℂ)‖ := Measurable.log (by fun_prop)
    exact this.aestronglyMeasurable
  · have hball : ∀ᶠ s in 𝓝 s0, ‖s - s0‖ < s0.re / 2 := by
      have := Metric.ball_mem_nhds s0 hr2
      filter_upwards [this] with s hs
      simpa [Metric.mem_ball, dist_eq_norm] using hs
    filter_upwards [hball] with s hs
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le hK] at hx
    obtain ⟨hx0, hxK⟩ := hx
    have hre : s0.re / 2 ≤ ‖s + (x : ℂ)‖ := by
      have h1 : (s + (x : ℂ)).re ≤ ‖s + (x : ℂ)‖ := Complex.re_le_norm _
      have h2 : |(s - s0).re| ≤ ‖s - s0‖ := Complex.abs_re_le_norm _
      have h3 := neg_abs_le (s - s0).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re] at h1 h3 h2
      linarith
    have hup : ‖s + (x : ℂ)‖ ≤ ‖s0‖ + s0.re / 2 + K := by
      calc ‖s + (x : ℂ)‖ = ‖(s - s0) + s0 + (x : ℂ)‖ := by ring_nf
        _ ≤ ‖s - s0‖ + ‖s0‖ + ‖(x : ℂ)‖ := norm_add₃_le
        _ ≤ s0.re / 2 + ‖s0‖ + K := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
        _ = _ := by ring
    rw [Real.norm_eq_abs]
    exact abs_log_le_of_mem hr2 hre hup
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le hK] at hx
    refine ContinuousAt.log (by fun_prop) ?_
    have : 0 < (s0 + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith [hx.1]
    exact norm_ne_zero_iff.mpr (fun h => by rw [h] at this; simp at this)

/-! ### G. Upper semicontinuity of `W_σ` -/

theorem wField_usc {e r B K θ : ℝ} (he : 0 ≤ e) (hr : 0 ≤ r) (hB : 0 < B) (hK : 0 ≤ K)
    {σ : Measure ℂ} [IsFiniteMeasure σ] {b A : ℝ} (hσ : BallMajA σ b A (1 / 2)) {s0 : ℂ}
    (hs0 : 0 < s0.re) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s - s0‖ < δ →
      wField e r B K θ σ s ≤ wField e r B K θ σ s0 + η := by
  obtain ⟨δ1, hδ1, h1⟩ := potC_usc_of hσ.b_pos hσ.ae_mem hσ.singleton_zero
    (integrable_log_norm_sub hσ) s0 (show 0 < η / 8 by positivity)
  have hBM := ballMaj_lebMeas hB
  obtain ⟨δ2, hδ2, h2⟩ := potC_usc_of hBM.b_pos hBM.ae_mem hBM.singleton_zero
    (integrable_log_norm_sub hBM) s0 (show 0 < η / (4 * (e + 1)) by positivity)
  have hcont := continuousAt_I2 hK hs0
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ3, hδ3, h3⟩ := hcont (η / (4 * (r + 1))) (by positivity)
  set δ4 : ℝ := η / (4 * (|θ| + 1)) with hδ4
  have hδ4p : 0 < δ4 := by positivity
  refine ⟨min (min δ1 δ2) (min δ3 δ4), lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4p), fun s hs => ?_⟩
  have hs1 : ‖s - s0‖ < δ1 := lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : ‖s - s0‖ < δ2 := lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : ‖s - s0‖ < δ3 := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ‖s - s0‖ < δ4 := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
  have e1 := h1 s hs1
  have e2 := h2 s hs2
  have e3 := h3 (by simpa [dist_eq_norm] using hs3)
  rw [Real.dist_eq] at e3
  have e4 : |(|s.im| - |s0.im|)| ≤ ‖s - s0‖ := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    have : (s - s0).im = s.im - s0.im := by simp
    rw [← this]
    exact Complex.abs_im_le_norm _
  have eI1 : potC (lebMeas B) s ≤ potC (lebMeas B) s0 + η / (4 * (e + 1)) := e2
  rw [potC_lebMeas hB.le, potC_lebMeas hB.le] at eI1
  rw [wField_eq_potC, wField_eq_potC]
  unfold CatalanCore.Decay.ComplexTaylor.vField
  have a1 : e * (∫ x in (0 : ℝ)..B, Real.log ‖s - (x : ℂ)‖) ≤
      e * (∫ x in (0 : ℝ)..B, Real.log ‖s0 - (x : ℂ)‖) + η / 4 := by
    have : e * (η / (4 * (e + 1))) ≤ η / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left eI1 he]
  have a2 : -(r * (∫ x in (0 : ℝ)..K, Real.log ‖s + (x : ℂ)‖)) ≤
      -(r * (∫ x in (0 : ℝ)..K, Real.log ‖s0 + (x : ℂ)‖)) + η / 4 := by
    have h5 := abs_lt.mp e3
    have : r * (η / (4 * (r + 1))) ≤ η / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h5.2.le hr, mul_le_mul_of_nonneg_left h5.1.le hr]
  have a3 : -(θ * |s.im|) ≤ -(θ * |s0.im|) + η / 4 := by
    have hb : |θ| * δ4 ≤ η / 4 := by
      rw [hδ4, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg θ]
    have hc : |θ| * ‖s - s0‖ ≤ η / 4 :=
      (mul_le_mul_of_nonneg_left hs4.le (abs_nonneg θ)).trans hb
    have hd : |θ * (|s.im| - |s0.im|)| ≤ |θ| * ‖s - s0‖ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left e4 (abs_nonneg θ)
    have := neg_abs_le (θ * (|s.im| - |s0.im|))
    nlinarith
  have a4 : 2 * potC σ s ≤ 2 * potC σ s0 + η / 4 := by linarith
  linarith

end CatalanCore.Lai.DecayDual


open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayDual

open CatalanCore.Lai CatalanCore.Decay.LemmaW CatalanCore.Decay.ComplexContour
  CatalanCore.Lai.DecayContour CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexEnergy
  CatalanCore.Decay.WedgeBounds CatalanCore.Tools.Joukowski
  CatalanCore.Decay.CurveFamily

/-! ### H. Bounds on one finite piece -/

/-- The weighted-curve bound constant of a finite piece with the data `n, ℓ', Rs`. -/
noncomputable def EB (n : ℕ) (ℓ' Rs : ℝ) : ℝ :=
  laiKC * Real.exp ((n : ℝ) * ℓ' + RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + Rs))

/-- Points of a piece at which Lemma W applies, with the field bound. -/
def PieceOK (σ : Measure ℂ) (n : ℕ) (ℓ' Rs : ℝ) (p : Piece) : Prop :=
  ∀ t ∈ Ioc (0 : ℝ) 1, GoodPt (p.zeta t) ∧
    wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) ≤ ℓ' ∧ ‖p.zeta t / (n : ℂ)‖ ≤ Rs

theorem PieceOK.conj {σ : Measure ℂ} (hσ : σ.map (starRingEnd ℂ) = σ) {n : ℕ} {ℓ' Rs : ℝ}
    {p : Piece} (h : PieceOK σ n ℓ' Rs p) : PieceOK σ n ℓ' Rs p.conj := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := h t ht
  rw [Piece.zeta_conj]
  refine ⟨h1.conj, ?_, ?_⟩
  · have : starRingEnd ℂ (p.zeta t) / (n : ℂ) = starRingEnd ℂ (p.zeta t / (n : ℂ)) := by simp
    rw [this, wField_conj _ _ _ _ _ hσ]; exact h2
  · have : starRingEnd ℂ (p.zeta t) / (n : ℂ) = starRingEnd ℂ (p.zeta t / (n : ℂ)) := by simp
    rw [this, Complex.norm_conj]; exact h3

/-- Pointwise bound of the weighted integrand on a piece with `‖κ‖ = (2π)⁻¹`. -/
theorem piece_pt_le (σ : Measure ℂ) (a b : ℝ) (hlam : 0 < 3 * |a| + |b|) {n : ℕ} (hn : 1 ≤ n)
    {ℓ' Rs : ℝ} {p : Piece} (hp : PieceOK σ n ℓ' Rs p) {κ : ℂ} (hκ : ‖κ‖ = (2 * Real.pi)⁻¹)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ * Real.exp (2 * n * potC σ ((Curve.ofPiece κ (rhoT n a b) p).ζ t / n))
      ≤ ‖p.D‖ * (2 * Real.pi)⁻¹ * EB n ℓ' Rs := by
  obtain ⟨h1, h2, h3⟩ := hp t ht
  have hb := rhoT_pt_le σ a b hlam n hn h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) + RConst 3 2 2 6 +
        4 * Real.log n + 3 * Real.log (1 + ‖p.zeta t / (n : ℂ)‖)) ≤
      Real.exp ((n : ℝ) * ℓ' + RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + Rs)) := by
    refine Real.exp_le_exp.mpr ?_
    have hr : Real.log (1 + ‖p.zeta t / (n : ℂ)‖) ≤ Real.log (1 + Rs) :=
      Real.log_le_log (by positivity) (by linarith)
    have := mul_le_mul_of_nonneg_left h2 hn0.le
    linarith
  show ‖κ * rhoT n a b (p.zeta t) * p.D‖ * Real.exp (2 * n * potC σ (p.zeta t / n)) ≤ _
  rw [norm_mul, norm_mul, hκ]
  calc (2 * Real.pi)⁻¹ * ‖rhoT n a b (p.zeta t)‖ * ‖p.D‖ * Real.exp (2 * n * potC σ (p.zeta t / n))
      = ‖p.D‖ * (2 * Real.pi)⁻¹ * (‖rhoT n a b (p.zeta t)‖ * Real.exp (2 * n * potC σ (p.zeta t / n))) := by ring
    _ ≤ ‖p.D‖ * (2 * Real.pi)⁻¹ * (laiKC * Real.exp ((n : ℝ) * ℓ' + RConst 3 2 2 6 +
          4 * Real.log n + 3 * Real.log (1 + Rs))) := by
        refine mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hE laiKC_nonneg
    _ = _ := by unfold EB; ring

end CatalanCore.Lai.DecayDual


open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayDual

open CatalanCore.Lai CatalanCore.Decay.LemmaW CatalanCore.Decay.ComplexContour
  CatalanCore.Lai.DecayContour CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexEnergy
  CatalanCore.Decay.WedgeBounds CatalanCore.Tools.Joukowski
  CatalanCore.Decay.CurveFamily

/-! ### I. The weight integral of one curve -/

/-- The integrand of the weight integral `hW` on one curve. -/
noncomputable def curveG (σ : Measure ℂ) (n : ℕ) (c : Curve) (t : ℝ) : ℝ :=
  ‖c.w t‖ * Real.exp (2 * n * potC σ (c.ζ t / n))

/-- `B` bounds the weight integral over the curve `c`, which is integrable. -/
def CurveBd (σ : Measure ℂ) (n : ℕ) (c : Curve) (B : ℝ) : Prop :=
  Integrable (curveG σ n c) c.ν ∧ ∫ t, curveG σ n c t ∂c.ν ≤ B

theorem Piece.nu_seg {p : Piece} (h : p.ray = false) : p.nu = volume.restrict (Ioc (0 : ℝ) 1) := by
  unfold Piece.nu; simp [h]

theorem Piece.nu_ray {p : Piece} (h : p.ray = true) : p.nu = volume.restrict (Ioi (0 : ℝ)) := by
  unfold Piece.nu; simp [h]

theorem curveG_nonneg (σ : Measure ℂ) (n : ℕ) (c : Curve) (t : ℝ) : 0 ≤ curveG σ n c t :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem measurable_curveG_piece (σ : Measure ℂ) [SFinite σ] (a b : ℝ) (n : ℕ) (p : Piece) (κ : ℂ) :
    Measurable (curveG σ n (Curve.ofPiece κ (rhoT n a b) p)) := by
  have hz : Continuous p.zeta := by unfold Piece.zeta; fun_prop
  have hw : Measurable fun t => ‖κ * rhoT n a b (p.zeta t) * p.D‖ :=
    ((measurable_const.mul ((measurable_rhoT n a b).comp hz.measurable)).mul measurable_const).norm
  have hp : Measurable fun t => potC σ (p.zeta t / n) :=
    (measurable_potC σ).comp (hz.measurable.div_const _)
  show Measurable fun t => ‖κ * rhoT n a b (p.zeta t) * p.D‖ * Real.exp (2 * n * potC σ (p.zeta t / n))
  exact hw.mul (Real.measurable_exp.comp (measurable_const.mul hp))

/-- Pointwise bound of the weight integrand at a good point of a piece. -/
theorem curveG_pt_le (σ : Measure ℂ) (a b : ℝ) (hlam : 0 < 3 * |a| + |b|) {n : ℕ} (hn : 1 ≤ n)
    {p : Piece} {κ : ℂ} (hκ : ‖κ‖ = (2 * Real.pi)⁻¹) {t : ℝ} (hg : GoodPt (p.zeta t)) :
    curveG σ n (Curve.ofPiece κ (rhoT n a b) p) t ≤ ‖p.D‖ * (2 * Real.pi)⁻¹ *
      (laiKC * Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) +
        RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + ‖p.zeta t / (n : ℂ)‖))) := by
  have hb := rhoT_pt_le σ a b hlam n hn hg
  show ‖κ * rhoT n a b (p.zeta t) * p.D‖ * Real.exp (2 * n * potC σ (p.zeta t / n)) ≤ _
  rw [norm_mul, norm_mul, hκ]
  calc (2 * Real.pi)⁻¹ * ‖rhoT n a b (p.zeta t)‖ * ‖p.D‖ * Real.exp (2 * n * potC σ (p.zeta t / n))
      = ‖p.D‖ * (2 * Real.pi)⁻¹ * (‖rhoT n a b (p.zeta t)‖ * Real.exp (2 * n * potC σ (p.zeta t / n))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

lemma EB_eq (n : ℕ) (hn : 1 ≤ n) (ℓ Rs : ℝ) (hRs : 0 ≤ Rs) :
    EB n ℓ Rs = laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 * (n : ℝ) ^ 4 * Real.exp (n * ℓ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : Real.exp (4 * Real.log n) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn0]
  have h3 : Real.exp (3 * Real.log (1 + Rs)) = (1 + Rs) ^ 3 := by
    rw [show (3 : ℝ) * Real.log (1 + Rs) = ((3 : ℕ) : ℝ) * Real.log (1 + Rs) by norm_num,
      Real.exp_nat_mul, Real.exp_log (by linarith)]
  unfold EB
  rw [Real.exp_add, Real.exp_add, Real.exp_add, h4, h3]
  ring

/-! ### II. A finite piece -/

/-- **(1) Finite piece.** -/
theorem curveBd_seg (σ : Measure ℂ) [IsFiniteMeasure σ] (a b : ℝ) (hlam : 0 < 3 * |a| + |b|)
    {n : ℕ} (hn : 1 ≤ n) {ℓ Rs : ℝ} {p : Piece} (hseg : p.ray = false) (hp : PieceOK σ n ℓ Rs p)
    {κ : ℂ} (hκ : ‖κ‖ = (2 * Real.pi)⁻¹) :
    CurveBd σ n (Curve.ofPiece κ (rhoT n a b) p)
      (‖p.D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 * (n : ℝ) ^ 4 *
        Real.exp (n * ℓ)) := by
  have hRs : 0 ≤ Rs := (norm_nonneg _).trans (hp 1 ⟨one_pos, le_rfl⟩).2.2
  have hbd : ∀ t ∈ Ioc (0 : ℝ) 1, curveG σ n (Curve.ofPiece κ (rhoT n a b) p) t ≤
      ‖p.D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 * (n : ℝ) ^ 4 *
        Real.exp (n * ℓ) := by
    intro t ht
    have h := piece_pt_le σ a b hlam hn hp hκ ht
    rw [EB_eq n hn ℓ Rs hRs] at h
    refine le_trans h (le_of_eq ?_)
    ring
  have hm := measurable_curveG_piece σ a b n p κ
  have hν : (Curve.ofPiece κ (rhoT n a b) p).ν = volume.restrict (Ioc (0 : ℝ) 1) := Piece.nu_seg hseg
  have hint : Integrable (curveG σ n (Curve.ofPiece κ (rhoT n a b) p)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    integrable_Ioc_of_le (M := ‖p.D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 *
      (n : ℝ) ^ 4 * Real.exp (n * ℓ)) hm.aestronglyMeasurable fun t ht => by
      rw [Real.norm_of_nonneg (curveG_nonneg _ _ _ _)]; exact hbd t ht
  rw [CurveBd, hν]
  exact ⟨hint, integral_Ioc_le hint hbd⟩

/-! ### III. A ray -/

/-- The points of a ray at which Lemma W applies, with the exponentially decaying field bound. -/
def RayOK (σ : Measure ℂ) (n : ℕ) (ℓ δ R0 : ℝ) (p : Piece) : Prop :=
  ∀ t ∈ Ioi (0 : ℝ), GoodPt (p.zeta t) ∧
    wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) ≤ ℓ - δ * (t / n) ∧
    ‖p.zeta t / (n : ℂ)‖ ≤ R0 + t / n

theorem RayOK.conj {σ : Measure ℂ} (hσ : σ.map (starRingEnd ℂ) = σ) {n : ℕ} {ℓ δ R0 : ℝ} {p : Piece}
    (h : RayOK σ n ℓ δ R0 p) : RayOK σ n ℓ δ R0 p.conj := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := h t ht
  have e : starRingEnd ℂ (p.zeta t) / (n : ℂ) = starRingEnd ℂ (p.zeta t / (n : ℂ)) := by simp
  rw [Piece.zeta_conj]
  refine ⟨h1.conj, ?_, ?_⟩
  · rw [e, wField_conj _ _ _ _ _ hσ]; exact h2
  · rw [e, Complex.norm_conj]; exact h3

theorem RayOK.mono_ell {σ : Measure ℂ} {n : ℕ} {ℓ ℓ' δ R0 : ℝ} {p : Piece} (hl : ℓ ≤ ℓ')
    (h : RayOK σ n ℓ δ R0 p) : RayOK σ n ℓ' δ R0 p := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := h t ht
  exact ⟨h1, by linarith, h3⟩

/-- **(2) Ray piece.**  The constant depends only on `δ` and `R0`. -/
theorem curveBd_ray {δ R0 : ℝ} (hδ : 0 < δ) (hR0 : 0 ≤ R0) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ (σ : Measure ℂ) [IsFiniteMeasure σ] (a b : ℝ) (_ : 0 < 3 * |a| + |b|)
      (n : ℕ) (_ : 1 ≤ n) (ℓ : ℝ) (p : Piece), p.ray = true → ‖p.D‖ = 1 → RayOK σ n ℓ δ R0 p →
      ∀ κ : ℂ, ‖κ‖ = (2 * Real.pi)⁻¹ →
      CurveBd σ n (Curve.ofPiece κ (rhoT n a b) p) (Cr * (n : ℝ) ^ 4 * Real.exp (n * ℓ)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := pow_one_add_le_exp 3 (show 0 < δ / 2 by positivity)
  refine ⟨2 / δ * ((2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + R0) ^ 3 * Cp),
    by have := laiKC_nonneg; positivity, ?_⟩
  intro σ _ a b hlam n hn ℓ p hray hD hp κ hκ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set M : ℝ := (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + R0) ^ 3 * Cp *
    ((n : ℝ) ^ 4 * Real.exp (n * ℓ)) with hM
  have hbd : ∀ t ∈ Ioi (0 : ℝ), curveG σ n (Curve.ofPiece κ (rhoT n a b) p) t ≤
      M * Real.exp (-(δ / 2) * t) := by
    intro t ht
    have ht0 : 0 < t := ht
    obtain ⟨hg, hW, hR⟩ := hp t ht
    have h := curveG_pt_le σ a b hlam hn hκ hg
    rw [hD] at h
    set x : ℝ := ‖p.zeta t / (n : ℂ)‖ with hx
    have hx0 : 0 ≤ x := norm_nonneg _
    have htn : t / n ≤ t := div_le_self ht0.le hn1
    have h1x : 1 + x ≤ (1 + R0) * (1 + t) := by nlinarith
    have hx3 : (1 + x) ^ 3 ≤ (1 + R0) ^ 3 * (1 + t) ^ 3 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1x 3
    have hn4 : Real.exp (4 * Real.log n) = (n : ℝ) ^ 4 := by
      rw [show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
        Real.exp_log hn0]
    have h3 : Real.exp (3 * Real.log (1 + x)) = (1 + x) ^ 3 := by
      rw [show (3 : ℝ) * Real.log (1 + x) = ((3 : ℕ) : ℝ) * Real.log (1 + x) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith)]
    have hnW : (n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) ≤ n * ℓ - δ * t := by
      have := mul_le_mul_of_nonneg_left hW hn0.le
      have e : (n : ℝ) * (ℓ - δ * (t / n)) = n * ℓ - δ * t := by field_simp
      linarith
    have hE : Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) +
        RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + x)) ≤
        Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) * (n : ℝ) ^ 4 * Real.exp (-δ * t) *
          ((1 + R0) ^ 3 * (1 + t) ^ 3) := by
      calc _ ≤ Real.exp ((n * ℓ - δ * t) + RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + x)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) * Real.exp (4 * Real.log n) *
              Real.exp (-δ * t) * Real.exp (3 * Real.log (1 + x)) := by
            simp only [← Real.exp_add]; congr 1; ring
        _ ≤ _ := by
            rw [h3, hn4]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact hx3
    have hpow := hCp t ht0.le
    have hexp : Real.exp (-δ * t) * Real.exp (δ / 2 * t) = Real.exp (-(δ / 2) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc curveG σ n (Curve.ofPiece κ (rhoT n a b) p) t
        ≤ 1 * (2 * Real.pi)⁻¹ * (laiKC * Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ
            (p.zeta t / (n : ℂ)) + RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + x))) := h
      _ ≤ 1 * (2 * Real.pi)⁻¹ * (laiKC * (Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) *
            (n : ℝ) ^ 4 * Real.exp (-δ * t) * ((1 + R0) ^ 3 * (1 + t) ^ 3))) := by
          have := laiKC_nonneg
          gcongr
      _ ≤ 1 * (2 * Real.pi)⁻¹ * (laiKC * (Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) *
            (n : ℝ) ^ 4 * Real.exp (-δ * t) * ((1 + R0) ^ 3 * (Cp * Real.exp (δ / 2 * t))))) := by
          have := laiKC_nonneg
          gcongr
      _ = M * Real.exp (-(δ / 2) * t) := by
          rw [hM, ← hexp]; ring
  have hm := measurable_curveG_piece σ a b n p κ
  have hν : (Curve.ofPiece κ (rhoT n a b) p).ν = volume.restrict (Ioi (0 : ℝ)) := Piece.nu_ray hray
  have hint : Integrable (curveG σ n (Curve.ofPiece κ (rhoT n a b) p)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_Ioi_of_le (μ := δ / 2) (M := M) (by positivity) hm.aestronglyMeasurable fun t ht => by
      rw [Real.norm_of_nonneg (curveG_nonneg _ _ _ _)]
      have : -(δ / 2) * t = -(δ / 2) * t := rfl
      exact hbd t ht
  rw [CurveBd, hν]
  refine ⟨hint, ?_⟩
  have := integral_Ioi_le (show 0 < δ / 2 by positivity) hint hbd
  refine this.trans (le_of_eq ?_)
  rw [hM]; field_simp

/-! ### IV. Lai's ray from `lai_tail_decay` -/

theorem lai_rayOK (σ : Measure ℂ) [IsFiniteMeasure σ] (hmass : σ.real univ = 3)
    (hsupp : ∀ᵐ u ∂σ, ‖(((21 / 10 : ℝ)) : ℂ) - u‖ ≤ 2091 / 1000)
    (hint : ∀ y : ℝ, 33 / 10 ≤ y →
      Integrable (fun u => Real.log ‖(((21 / 10 : ℝ)) : ℂ) + y * Complex.I - u‖) σ)
    {n : ℕ} (hn : 1 ≤ n) {p : Piece} (hray : p.ray = true) (hD : p.D = Complex.I)
    (ha : p.a = (n : ℂ) * (((21 / 10 : ℝ) : ℂ) + ((33 / 10 : ℝ) : ℂ) * Complex.I)) :
    RayOK σ n (-130471 / 10000) (1 / 40) (27 / 5) p := by
  intro t ht
  have ht0 : 0 < t := ht
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hz : p.zeta t / (n : ℂ) =
      (((21 / 10 : ℝ)) : ℂ) + ((33 / 10 + t / n : ℝ) : ℂ) * Complex.I := by
    unfold Piece.zeta
    rw [ha, hD]
    push_cast
    field_simp
    ring
  have hy : (33 / 10 : ℝ) ≤ 33 / 10 + t / n := by
    have : 0 ≤ t / n := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hre : (p.zeta t).re = 21 * n / 10 := by
      unfold Piece.zeta; rw [ha, hD]; simp; ring
    have him : (p.zeta t).im = 33 * n / 10 + t := by
      unfold Piece.zeta; rw [ha, hD]; simp; ring
    have him1 : 1 ≤ |(p.zeta t).im| := by
      rw [him, abs_of_pos (by positivity)]; linarith
    refine ⟨?_, ?_, ?_, Or.inl him1⟩
    · intro h0; rw [h0] at him1; simp at him1; linarith
    · rw [hre]; positivity
    · have := Complex.abs_im_le_norm (p.zeta t); linarith
  · rw [hz]
    have := CatalanCore.Lai.DecayTail.lai_tail_decay hmass hsupp hint hy
    have h2 : (1 / 40 : ℝ) * (t / n) ≤ (1 / 40) * (33 / 10 + t / n) := by
      have : (0 : ℝ) ≤ 33 / 10 := by norm_num
      nlinarith
    linarith
  · rw [hz]
    calc ‖(((21 / 10 : ℝ)) : ℂ) + ((33 / 10 + t / n : ℝ) : ℂ) * Complex.I‖
        ≤ ‖(((21 / 10 : ℝ)) : ℂ)‖ + ‖((33 / 10 + t / n : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 21 / 10 + (33 / 10 + t / n) := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg (by positivity)]
      _ = 27 / 5 + t / n := by ring

/-! ### V. Atoms -/

lemma omegaFun_eq (x : ℝ) : omegaFun 3 2 2 6 x = omegaF 3 2 2 6 x := by
  unfold omegaFun omegaF xl
  push_cast
  ring

/-- `C(6n,k)² C(2n+k,k)³ · e^{2n U(-k/n)} ≤ e^{n a*}`. -/
theorem atom_coef_le (σ : Measure ℂ) [IsFiniteMeasure σ] {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ 6 * n)
    {astar : ℝ} (hat : ∀ x ∈ Icc (0 : ℝ) 6,
      omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ astar) :
    (laiCoef n k : ℝ) * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n)) ≤ Real.exp (n * astar) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := log_atom_le 3 2 2 6 n k hn (by omega)
  have hpos : (0 : ℝ) < (laiCoef n k : ℝ) := by
    unfold laiCoef
    have h1 : 0 < (6 * n).choose k := Nat.choose_pos hk
    have h2 : 0 < (2 * n + k).choose k := Nat.choose_pos (by omega)
    exact_mod_cast Nat.mul_pos (pow_pos h1 2) (pow_pos h2 3)
  have hcoef : (laiCoef n k : ℝ) = (((6 * n).choose k : ℝ)) ^ 2 * (((2 * n + k).choose k : ℝ)) ^ 3 := by
    unfold laiCoef; push_cast; ring
  have hx : (k : ℝ) / n ∈ Icc (0 : ℝ) 6 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hn0]
    have : (k : ℝ) ≤ 6 * n := by exact_mod_cast hk
    linarith
  have hU : potC σ ((-(k : ℂ)) / n) = ∫ u, Real.log ‖(((k : ℝ) / n : ℝ) : ℂ) + u‖ ∂σ := by
    unfold potC
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show Real.log ‖(-(k : ℂ)) / n - u‖ = _
    rw [← norm_neg]
    congr 2
    push_cast
    ring
  have h1 : (laiCoef n k : ℝ) ≤ Real.exp (n * omegaFun 3 2 2 6 ((k : ℝ) / n)) := by
    have hlog' : Real.log (laiCoef n k : ℝ) ≤ n * omegaFun 3 2 2 6 ((k : ℝ) / n) := by
      rw [hcoef]; exact hlog
    exact (Real.log_le_iff_le_exp hpos).mp hlog'
  have hat' := hat _ hx
  rw [← hU, ← omegaFun_eq] at hat'
  calc (laiCoef n k : ℝ) * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n))
      ≤ Real.exp (n * omegaFun 3 2 2 6 ((k : ℝ) / n)) * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (n * (omegaFun 3 2 2 6 ((k : ℝ) / n) + 2 * potC σ ((-(k : ℂ)) / n))) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (n * astar) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hat' hn0.le)

/-- **(4) Atom.** -/
theorem curveBd_atom (σ : Measure ℂ) [IsFiniteMeasure σ] {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ 6 * n)
    {astar : ℝ} (hat : ∀ x ∈ Icc (0 : ℝ) 6,
      omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ astar)
    {α : ℂ} {q ρ ℓ : ℝ} (hq : 0 ≤ q) (hα : ‖α‖ ≤ q * Real.exp (-(ρ * n)) * (laiCoef n k : ℝ))
    (hρ : astar ≤ ℓ + ρ) :
    CurveBd σ n (Curve.atom (-(k : ℂ)) α) (q * Real.exp (n * ℓ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := atom_coef_le σ hn hk hat
  have hG : curveG σ n (Curve.atom (-(k : ℂ)) α) = fun _ => ‖α‖ * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n)) := rfl
  have hν : (Curve.atom (-(k : ℂ)) α).ν = Measure.dirac 0 := rfl
  have hle : ‖α‖ * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n)) ≤ q * Real.exp (n * ℓ) := by
    calc ‖α‖ * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n))
        ≤ (q * Real.exp (-(ρ * n)) * (laiCoef n k : ℝ)) * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n)) :=
          mul_le_mul_of_nonneg_right hα (Real.exp_pos _).le
      _ = q * Real.exp (-(ρ * n)) * ((laiCoef n k : ℝ) * Real.exp (2 * n * potC σ ((-(k : ℂ)) / n))) := by
          ring
      _ ≤ q * Real.exp (-(ρ * n)) * Real.exp (n * astar) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = q * Real.exp (-(ρ * n) + n * astar) := by rw [mul_assoc, Real.exp_add]
      _ ≤ q * Real.exp (n * ℓ) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hq
          nlinarith
  rw [CurveBd, hν, hG]
  refine ⟨integrable_const _, ?_⟩
  simpa using hle

/-! ### VI. The list and `hW` -/

/-- The atoms `-k` (`k ≤ 6n`) with weights `α k`. -/
noncomputable def atomCurves (n : ℕ) (α : ℕ → ℂ) : List Curve :=
  (List.range (6 * n + 1)).map fun k : ℕ => Curve.atom (-(k : ℂ)) (α k)

theorem listG_integral (σ : Measure ℂ) (n : ℕ) (cs : List Curve)
    (hc : ∀ c ∈ cs, Integrable (curveG σ n c) c.ν) :
    Integrable (fun x => ‖listW cs x‖ * Real.exp (2 * n * potC σ (listZ cs x / n))) (listMeasure cs) ∧
    ∫ x, ‖listW cs x‖ * Real.exp (2 * n * potC σ (listZ cs x / n)) ∂listMeasure cs =
      (cs.map fun c => ∫ t, curveG σ n c t ∂c.ν).sum := by
  have hi := (integrable_list_iff cs (fun w z => ‖w‖ * Real.exp (2 * n * potC σ (z / n)))).mpr hc
  exact ⟨hi, integral_list cs (fun w z => ‖w‖ * Real.exp (2 * n * potC σ (z / n))) hi⟩

/-- **(5a) The list bound.** -/
theorem listG_bound (σ : Measure ℂ) (n : ℕ) (cs : List Curve) (B : Curve → ℝ)
    (hB : ∀ c ∈ cs, CurveBd σ n c (B c)) :
    Integrable (fun x => ‖listW cs x‖ * Real.exp (2 * n * potC σ (listZ cs x / n))) (listMeasure cs) ∧
    ∫ x, ‖listW cs x‖ * Real.exp (2 * n * potC σ (listZ cs x / n)) ∂listMeasure cs ≤
      (cs.map B).sum := by
  obtain ⟨hi, he⟩ := listG_integral σ n cs fun c hc => (hB c hc).1
  refine ⟨hi, ?_⟩
  rw [he]
  exact List.sum_le_sum fun c hc => (hB c hc).2

/-- **(5b) `hW` for Lai's weight space** (pieces + atoms), in the form `C n⁴ e^{nℓ}`. -/
theorem lai_hW (σ : Measure ℂ) [IsFiniteMeasure σ] {n : ℕ} (hn : 1 ≤ n) {ℓ astar ρ q : ℝ}
    (hq : 0 ≤ q) (hρ : astar ≤ ℓ + ρ)
    (hat : ∀ x ∈ Icc (0 : ℝ) 6, omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ astar)
    (α : ℕ → ℂ) (hα : ∀ k ≤ 6 * n, ‖α k‖ ≤ q * Real.exp (-(ρ * n)) * (laiCoef n k : ℝ))
    (Pcs : List Curve) (C : Curve → ℝ)
    (hP : ∀ c ∈ Pcs, CurveBd σ n c (C c * (n : ℝ) ^ 4 * Real.exp (n * ℓ))) :
    Integrable (fun x => ‖listW (Pcs ++ atomCurves n α) x‖ *
        Real.exp (2 * n * potC σ (listZ (Pcs ++ atomCurves n α) x / n)))
      (listMeasure (Pcs ++ atomCurves n α)) ∧
    ∫ x, ‖listW (Pcs ++ atomCurves n α) x‖ *
        Real.exp (2 * n * potC σ (listZ (Pcs ++ atomCurves n α) x / n)) ∂listMeasure (Pcs ++ atomCurves n α) ≤
      ((Pcs.map C).sum + 7 * q) * (n : ℝ) ^ 4 * Real.exp (n * ℓ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAt : ∀ c ∈ atomCurves n α, CurveBd σ n c (q * Real.exp (n * ℓ)) := by
    intro c hc
    unfold atomCurves at hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact curveBd_atom σ hn (by omega) hat hq (hα k (by omega)) hρ
  obtain ⟨hi, he⟩ := listG_integral σ n (Pcs ++ atomCurves n α) fun c hc => by
    rcases List.mem_append.mp hc with h | h
    · exact (hP c h).1
    · exact (hAt c h).1
  refine ⟨hi, ?_⟩
  rw [he, List.map_append, List.sum_append]
  have h1 : (Pcs.map fun c => ∫ t, curveG σ n c t ∂c.ν).sum ≤
      (Pcs.map fun c => C c * (n : ℝ) ^ 4 * Real.exp (n * ℓ)).sum :=
    List.sum_le_sum fun c hc => (hP c hc).2
  have h2 : ((atomCurves n α).map fun c => ∫ t, curveG σ n c t ∂c.ν).sum ≤
      (6 * n + 1 : ℕ) • (q * Real.exp (n * ℓ)) := by
    have := List.sum_le_card_nsmul ((atomCurves n α).map fun c => ∫ t, curveG σ n c t ∂c.ν)
      (q * Real.exp (n * ℓ)) (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact (hAt c hc).2)
    simpa [atomCurves] using this
  rw [List.sum_map_mul_right, List.sum_map_mul_right] at h1
  rw [nsmul_eq_mul] at h2
  have h3 : ((6 * n + 1 : ℕ) : ℝ) * (q * Real.exp (n * ℓ)) ≤ 7 * q * (n : ℝ) ^ 4 * Real.exp (n * ℓ) := by
    push_cast
    have hn4 : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
    have hE := (Real.exp_pos (n * ℓ)).le
    have : (6 * (n : ℝ) + 1) * q ≤ 7 * q * (n : ℝ) ^ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hE]
  nlinarith [h1, h2, h3]

/-- **(5c) `hW` in the exponential form of `theoremA_eventually`** (`L = 4`, `c₀ = log Ctot`). -/
theorem lai_hW_exp (σ : Measure ℂ) [IsFiniteMeasure σ] {n : ℕ} (hn : 1 ≤ n) {ℓ astar ρ q : ℝ}
    (hq : 0 ≤ q) (hρ : astar ≤ ℓ + ρ)
    (hat : ∀ x ∈ Icc (0 : ℝ) 6, omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ astar)
    (α : ℕ → ℂ) (hα : ∀ k ≤ 6 * n, ‖α k‖ ≤ q * Real.exp (-(ρ * n)) * (laiCoef n k : ℝ))
    (Pcs : List Curve) (C : Curve → ℝ)
    (hP : ∀ c ∈ Pcs, CurveBd σ n c (C c * (n : ℝ) ^ 4 * Real.exp (n * ℓ)))
    {Ctot : ℝ} (h0 : 0 < Ctot) (hC : (Pcs.map C).sum + 7 * q ≤ Ctot) :
    Integrable (fun x => ‖listW (Pcs ++ atomCurves n α) x‖ *
        Real.exp (2 * n * potC σ (listZ (Pcs ++ atomCurves n α) x / n)))
      (listMeasure (Pcs ++ atomCurves n α)) ∧
    ∫ x, ‖listW (Pcs ++ atomCurves n α) x‖ *
        Real.exp (2 * n * potC σ (listZ (Pcs ++ atomCurves n α) x / n)) ∂listMeasure (Pcs ++ atomCurves n α) ≤
      Real.exp (n * ℓ + 4 * Real.log n + Real.log Ctot) := by
  obtain ⟨hi, hb⟩ := lai_hW σ hn hq hρ hat α hα Pcs C hP
  refine ⟨hi, hb.trans ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : Real.exp (4 * Real.log n) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn0]
  have : Real.exp (n * ℓ + 4 * Real.log n + Real.log Ctot) = Ctot * (n : ℝ) ^ 4 * Real.exp (n * ℓ) := by
    rw [Real.exp_add, Real.exp_add, h4, Real.exp_log h0]; ring
  rw [this]
  have hE := (Real.exp_pos (n * ℓ)).le
  have hp4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hp4) hE

end CatalanCore.Lai.DecayDual


open MeasureTheory Set Real Filter Topology Finset Polynomial

namespace CatalanCore.Lai.DecayDual

open CatalanCore.Uniform.Decay.Polygon (polyI)
open CatalanCore.Lai CatalanCore.Decay.LemmaW CatalanCore.Decay.ComplexContour
  CatalanCore.Lai.DecayContour CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexEnergy
  CatalanCore.Decay.WedgeBounds CatalanCore.Tools.Joukowski
  CatalanCore.Decay.CurveFamily

/-! ### I. Geometry of the pieces of an admissible polygon -/

lemma chainPieces_im (a : ℂ) (l : List ℂ) (ha : 0 ≤ a.im) (hl : ∀ z ∈ l, 0 < z.im) :
    ∀ p ∈ chainPieces (a :: l), p.ray = false ∧ 0 ≤ p.a.im ∧ 0 < (p.a + p.D).im := by
  induction l generalizing a with
  | nil => intro p hp; simp [chainPieces] at hp
  | cons b rest ih =>
    intro p hp
    simp only [chainPieces, List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨rfl, ha, ?_⟩
      simp only [add_sub_cancel]
      exact hl b (by simp)
    · exact ih b (le_of_lt (hl b (by simp))) (fun z hz => hl z (List.mem_cons_of_mem _ hz)) p
        (by simpa [chainPieces] using hp)

/-- Every point of a piece (`t ∈ (0, 1]` for a segment, `t > 0` for the ray) lies in the open upper
half plane when the polygon starts on the real axis and the other vertices are above it. -/
lemma polyPieces_im (v : ℂ) (pts : List ℂ) (d : ℂ) (hv : v.im = 0) (hpts : ∀ z ∈ pts, 0 < z.im)
    (hd : 0 < d.im) :
    ∀ p ∈ polyPieces (v :: pts) (List.cons_ne_nil _ _) d, ∀ t : ℝ, 0 < t →
      (p.ray = true ∨ t ≤ 1) → 0 < (p.zeta t).im := by
  intro p hp t ht hr
  unfold polyPieces at hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨hray, ha, hb⟩ := chainPieces_im v pts (by rw [hv]) hpts p hp
    have ht1 : t ≤ 1 := by
      rcases hr with h | h
      · rw [hray] at h; exact absurd h (by simp)
      · exact h
    have e : (p.zeta t).im = p.a.im + t * p.D.im := by
      simp [Piece.zeta, Complex.mul_im]
    have hb' : 0 < p.a.im + p.D.im := by simpa using hb
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) ha, mul_pos ht (show 0 < p.a.im + p.D.im from hb')]
  · simp only [List.mem_singleton] at hp
    subst hp
    have hlast : 0 ≤ ((v :: pts).getLast (List.cons_ne_nil _ _)).im := by
      have hm := List.getLast_mem (List.cons_ne_nil v pts)
      rcases List.mem_cons.mp hm with h | h
      · rw [h, hv]
      · exact (hpts _ h).le
    have e : (Piece.zeta ⟨(v :: pts).getLast (List.cons_ne_nil _ _), d, true⟩ t).im =
        ((v :: pts).getLast (List.cons_ne_nil _ _)).im + t * d.im := by
      simp [Piece.zeta, Complex.mul_im]
    rw [e]
    nlinarith [mul_pos ht hd]

lemma chainPieces_map_conj : ∀ l : List ℂ,
    chainPieces (l.map (starRingEnd ℂ)) = (chainPieces l).map Piece.conj
  | [] => by simp [chainPieces]
  | [a] => by simp [chainPieces]
  | a :: b :: rest => by
    have ih := chainPieces_map_conj (b :: rest)
    simp only [List.map_cons] at ih ⊢
    simp only [chainPieces, List.map_cons, ih, Piece.conj, map_sub]

lemma polyPieces_conj (v : ℝ) (pts : List ℂ) (d : ℂ) :
    polyPieces ((v : ℂ) :: pts.map (starRingEnd ℂ)) (List.cons_ne_nil _ _) (starRingEnd ℂ d) =
      (polyPieces ((v : ℂ) :: pts) (List.cons_ne_nil _ _) d).map Piece.conj := by
  unfold polyPieces
  rw [List.map_append]
  congr 1
  · have h := chainPieces_map_conj ((v : ℂ) :: pts)
    simpa [Complex.conj_ofReal] using h
  · have h := List.getLast_map (f := starRingEnd ℂ) (l := (v : ℂ) :: pts) (List.cons_ne_nil _ _)
    simp only [List.map_cons, Complex.conj_ofReal] at h
    simp only [List.map_cons, List.map_nil, Piece.conj, List.cons.injEq, and_true]
    rw [h]

/-! ### II. The curve list of the weight `λ⁻¹ R_n K_c` on `Γ ∪ Γ̄` and the perturbation atoms -/

/-- The norm `λ = ‖c‖ = 3|a| + |b|` of the jet coefficients `c = (-3a, b)`. -/
noncomputable abbrev laiLam (a b : ℝ) : ℝ := 3 * |a| + |b|

/-- `κ = (2πi)⁻¹`, of norm `(2π)⁻¹`. -/
noncomputable def kap : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

lemma norm_kap : ‖kap‖ = (2 * Real.pi)⁻¹ := by
  unfold kap
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real]
  simp [abs_of_pos Real.pi_pos]

lemma norm_neg_kap : ‖-kap‖ = (2 * Real.pi)⁻¹ := by rw [norm_neg, norm_kap]

/-- The pieces of the upper half `Γ`: `v → pts → ∞ d`. -/
noncomputable def laiPieces (v : ℝ) (pts : List ℂ) (d : ℂ) : List Piece :=
  polyPieces ((v : ℂ) :: pts) (List.cons_ne_nil _ _) d

/-- The weighted curves: the upper half with weight `-κ λ⁻¹ R_n K_c dz`, the lower half (mirror
image) with weight `κ λ⁻¹ R_n K_c dz`, and the atoms `6 t c_k / λ` at `-k`, `0 ≤ k ≤ 6n`. -/
noncomputable def laiCurves (n : ℕ) (a b t v : ℝ) (pts : List ℂ) (d : ℂ) : List Curve :=
  (laiPieces v pts d).map (Curve.ofPiece (-kap) (rhoT n a b)) ++
  ((laiPieces v pts d).map Piece.conj).map (Curve.ofPiece kap (rhoT n a b)) ++
  (List.range (6 * n + 1)).map (fun k : ℕ =>
    Curve.atom (-(k : ℂ)) (((6 * t * (laiCoef n k : ℝ) / laiLam a b : ℝ)) : ℂ))

lemma sum_list_range (f : ℕ → ℂ) : ∀ m : ℕ,
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
      sum_list_range f m]
    simp

lemma piece_integral (κ : ℂ) (p : Piece) (n k : ℕ) (a b : ℝ) (hlam : 0 < laiLam a b)
    (hk : k < 6 * n)
    (him : ∀ s : ℝ, 0 < s → (p.ray = true ∨ s ≤ 1) → (p.zeta s).im ≠ 0) :
    ∫ s, (Curve.ofPiece κ (rhoT n a b) p).w s * (Curve.ofPiece κ (rhoT n a b) p).ζ s ^ k
        ∂(Curve.ofPiece κ (rhoT n a b) p).ν =
      κ / (laiLam a b : ℂ) * ∫ s, laiIntegrand n (X ^ k) a b (p.zeta s) * p.D ∂p.nu := by
  have hlc : (laiLam a b : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  show ∫ s, (κ * rhoT n a b (p.zeta s) * p.D) * p.zeta s ^ k ∂p.nu = _
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂p.nu, 0 < s ∧ (p.ray = true ∨ s ≤ 1) := by
    unfold Piece.nu
    cases h : p.ray
    · simp only [Bool.false_eq_true, ↓reduceIte]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact ⟨hs.1, by simp [hs.2]⟩
    · simp only [↓reduceIte]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact ⟨hs, by simp⟩
  filter_upwards [hae] with s hs
  rw [laiIntegrand_eq_rho n k hk a b (him s hs.1 hs.2)]
  simp only [rhoT]
  field_simp

lemma pieces_integral (κ : ℂ) (ps : List Piece) (n k : ℕ) (a b : ℝ) (hlam : 0 < laiLam a b)
    (hk : k < 6 * n)
    (him : ∀ p ∈ ps, ∀ s : ℝ, 0 < s → (p.ray = true ∨ s ≤ 1) → (p.zeta s).im ≠ 0) :
    ((ps.map (Curve.ofPiece κ (rhoT n a b))).map
        fun c => ∫ s, c.w s * c.ζ s ^ k ∂c.ν).sum =
      κ / (laiLam a b : ℂ) *
        (ps.map fun p => ∫ s, laiIntegrand n (X ^ k) a b (p.zeta s) * p.D ∂p.nu).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  exact piece_integral κ p n k a b hlam hk (him p hp)

lemma atoms_integral (n k : ℕ) (a b t : ℝ) :
    (((List.range (6 * n + 1)).map (fun j : ℕ =>
        Curve.atom (-(j : ℂ)) (((6 * t * (laiCoef n j : ℝ) / laiLam a b : ℝ)) : ℂ))).map
      fun c => ∫ s, c.w s * c.ζ s ^ k ∂c.ν).sum =
    ∑ j ∈ Finset.range (6 * n + 1),
      (((6 * t * (laiCoef n j : ℝ) / laiLam a b : ℝ)) : ℂ) * (-(j : ℂ)) ^ k := by
  rw [List.map_map, sum_list_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Curve.atom, Function.comp]

lemma pieces_im_ne (v : ℝ) (pts : List ℂ) (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    ∀ p ∈ laiPieces v pts d, ∀ s : ℝ, 0 < s → (p.ray = true ∨ s ≤ 1) → (p.zeta s).im ≠ 0 :=
  fun p hp s hs hr => (polyPieces_im (v : ℂ) pts d (by simp) hpts hd p hp s hs hr).ne'

lemma pieces_conj_im_ne (v : ℝ) (pts : List ℂ) (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ}
    (hd : 0 < d.im) :
    ∀ p ∈ (laiPieces v pts d).map Piece.conj, ∀ s : ℝ, 0 < s → (p.ray = true ∨ s ≤ 1) →
      (p.zeta s).im ≠ 0 := by
  intro p hp s hs hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have := pieces_im_ne v pts hpts hd q hq s hs hr
  rw [Piece.zeta_conj, Complex.conj_im]
  exact neg_ne_zero.mpr this

/-- **One entry**: `L_n(t^k)(a, b, aζ(3) + bζ(4) + t) = λ ∑_{c ∈ curves} ∫ c.w c.ζ^k dc.ν`. -/
theorem entry_eq (n k : ℕ) (hk : k < 6 * n) (a b t v : ℝ) (hlam : 0 < laiLam a b)
    (hv0 : 0 < v) (hv2 : v < 2 * n + 1) (hvm : ∀ m : ℤ, v ≠ m) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    ((MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiL n (X ^ k)) : ℝ) : ℂ) =
      (laiLam a b : ℂ) * ((laiCurves n a b t v pts d).map
        fun c => ∫ s, c.w s * c.ζ s ^ k ∂c.ν).sum := by
  have hdeg : (X ^ k : ℚ[X]).degree < ((6 * n : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]; exact_mod_cast hk
  have hlc : (laiLam a b : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  rw [laiL_perturb, Complex.ofReal_add, laiL_contour n (X ^ k) hdeg a b v hv0 hv2 hvm pts hpts hd]
  have hatoms : (((6 * t * ∑ j ∈ range (6 * n + 1), (laiCoef n j : ℝ) *
      (((X ^ k : ℚ[X]).eval (-(j : ℚ)) : ℚ) : ℝ) : ℝ)) : ℂ) =
      (laiLam a b : ℂ) * ∑ j ∈ Finset.range (6 * n + 1),
        (((6 * t * (laiCoef n j : ℝ) / laiLam a b : ℝ)) : ℂ) * (-(j : ℂ)) ^ k := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [eval_pow, eval_X]
    push_cast
    have hlc2 : (3 * ((|a| : ℝ) : ℂ) + ((|b| : ℝ) : ℂ)) ≠ 0 := by
      have := hlc; push_cast at this; exact this
    field_simp
  have hup : polyI (laiIntegrand n (X ^ k) a b) (v : ℂ) pts d =
      ((laiPieces v pts d).map fun p => ∫ s, laiIntegrand n (X ^ k) a b (p.zeta s) * p.D ∂p.nu).sum :=
    polyI_eq_sum _ _ _ _
  have hlow : polyI (laiIntegrand n (X ^ k) a b) (v : ℂ) (pts.map (starRingEnd ℂ))
      (starRingEnd ℂ d) =
      (((laiPieces v pts d).map Piece.conj).map
        fun p => ∫ s, laiIntegrand n (X ^ k) a b (p.zeta s) * p.D ∂p.nu).sum := by
    rw [polyI_eq_sum, polyPieces_conj]; rfl
  unfold laiCurves
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
    pieces_integral (-kap) _ n k a b hlam hk (pieces_im_ne v pts hpts hd),
    pieces_integral kap _ n k a b hlam hk (pieces_conj_im_ne v pts hpts hd), atoms_integral,
    hup, hlow, hatoms]
  unfold kap
  field_simp
  ring

/-- **The matrix identity**: `J_n(a, b, aζ(3) + bζ(4) + t)` is `λ^{3n} / ∏ i!²` times the Hankel
determinant of the moments of the weighted curve family. -/
theorem laiJ_eq_det (n : ℕ) (a b t v : ℝ) (hlam : 0 < laiLam a b)
    (hv0 : 0 < v) (hv2 : v < 2 * n + 1) (hvm : ∀ m : ℤ, v ≠ m) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im)
    (hint : ∀ i j : Fin (3 * n),
      Integrable (fun x => listW (laiCurves n a b t v pts d) x *
        listZ (laiCurves n a b t v pts d) x ^ ((i : ℕ) + (j : ℕ)))
        (listMeasure (laiCurves n a b t v pts d))) :
    ((MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n) : ℝ) : ℂ) =
      (((∏ i ∈ range (3 * n), ((i.factorial : ℝ)) ^ 2)⁻¹ : ℝ) : ℂ) * (laiLam a b : ℂ) ^ (3 * n) *
        (Matrix.of fun i j : Fin (3 * n) =>
          ∫ x, listW (laiCurves n a b t v pts d) x * listZ (laiCurves n a b t v pts d) x ^
            ((i : ℕ) + (j : ℕ)) ∂listMeasure (laiCurves n a b t v pts d)).det := by
  have hreal : MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n) =
      ((∏ i ∈ range (3 * n), ((i.factorial : ℝ)) ^ 2)⁻¹) *
        (Matrix.of fun i j : Fin (3 * n) =>
          MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t]
            (laiL n (X ^ ((i : ℕ) + j)))).det := by
    unfold laiJ laiMat
    rw [map_mul, MvPolynomial.aeval_C, AlgHom.map_det]
    congr 1
    simp only [eq_ratCast]; push_cast; try rfl
  rw [hreal, Complex.ofReal_mul]
  have hdet : (((Matrix.of fun i j : Fin (3 * n) =>
        MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t]
          (laiL n (X ^ ((i : ℕ) + j)))).det : ℝ) : ℂ) =
      (laiLam a b : ℂ) ^ (3 * n) *
        (Matrix.of fun i j : Fin (3 * n) =>
          ∫ x, listW (laiCurves n a b t v pts d) x * listZ (laiCurves n a b t v pts d) x ^
            ((i : ℕ) + (j : ℕ)) ∂listMeasure (laiCurves n a b t v pts d)).det := by
    rw [show (((Matrix.of fun i j : Fin (3 * n) =>
        MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t]
          (laiL n (X ^ ((i : ℕ) + j)))).det : ℝ) : ℂ) = Complex.ofRealHom _ from rfl,
      RingHom.map_det]
    have hM : Complex.ofRealHom.mapMatrix (Matrix.of fun i j : Fin (3 * n) =>
        MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t]
          (laiL n (X ^ ((i : ℕ) + j)))) =
        (laiLam a b : ℂ) • (Matrix.of fun i j : Fin (3 * n) =>
          ∫ x, listW (laiCurves n a b t v pts d) x * listZ (laiCurves n a b t v pts d) x ^
            ((i : ℕ) + (j : ℕ)) ∂listMeasure (laiCurves n a b t v pts d)) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      have hk : (i : ℕ) + (j : ℕ) < 6 * n := by have := i.2; have := j.2; omega
      rw [show Complex.ofRealHom _ = ((_ : ℝ) : ℂ) from rfl,
        entry_eq n _ hk a b t v hlam hv0 hv2 hvm pts hpts hd]
      congr 1
      exact (integral_list (laiCurves n a b t v pts d)
        (fun w z => w * z ^ ((i : ℕ) + (j : ℕ))) (hint i j)).symm
    rw [hM, Matrix.det_smul, Fintype.card_fin]
  rw [hdet]
  ring

/-! ### III. Integrability of the curve family -/

lemma integrable_Ioc_of_bdd {E : Type*} [NormedAddCommGroup E] {F : ℝ → E} {M : ℝ}
    (hm : AEStronglyMeasurable F volume) (h : ∀ t ∈ Ioc (0 : ℝ) 1, ‖F t‖ ≤ M) :
    Integrable F (volume.restrict (Ioc (0 : ℝ) 1)) := by
  refine Integrable.mono' (integrable_const M) hm.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using h t ht

lemma integrable_Ioi_of_expb {E : Type*} [NormedAddCommGroup E] {F : ℝ → E} {M μ : ℝ}
    (hμ : 0 < μ) (hm : AEStronglyMeasurable F volume)
    (h : ∀ t ∈ Ioi (0 : ℝ), ‖F t‖ ≤ M * Real.exp (-μ * t)) :
    Integrable F (volume.restrict (Ioi (0 : ℝ))) := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-μ * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -μ < 0) 0).const_mul M
  refine Integrable.mono' hint hm.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using h t ht

lemma norm_le_of_potC {σ : Measure ℂ} [IsFiniteMeasure σ] {bb A : ℝ}
    (hσ : BallMajA σ bb A (1 / 2)) (n : ℕ) (z : ℂ) {x M : ℝ} (hx : 0 ≤ x)
    (h : x * Real.exp (2 * n * potC σ z) ≤ M) : x ≤ M * Real.exp (4 * n * A) := by
  have hp := CatalanCore.Decay.CurveFamily.neg_le_potC_half hσ z
  have e : A * (1 : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * A := by rw [Real.one_rpow]; ring
  rw [e] at hp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp (-(2 * n * potC σ z)) ≤ Real.exp (4 * n * A) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc x = x * Real.exp (2 * n * potC σ z) * Real.exp (-(2 * n * potC σ z)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ M * Real.exp (4 * n * A) :=
        mul_le_mul h h1 (Real.exp_pos _).le ((mul_nonneg hx (Real.exp_pos _).le).trans h)

lemma measurable_zeta (p : Piece) : Measurable p.zeta := by
  unfold Piece.zeta
  fun_prop

lemma measurable_ofPiece_w (κ : ℂ) (n : ℕ) (a b : ℝ) (p : Piece) :
    Measurable (Curve.ofPiece κ (rhoT n a b) p).w := by
  show Measurable fun t : ℝ => κ * rhoT n a b (p.zeta t) * p.D
  exact (measurable_const.mul ((measurable_rhoT n a b).comp (measurable_zeta p))).mul
    measurable_const

lemma measurable_weightE (σ : Measure ℂ) [SFinite σ] (κ : ℂ) (n : ℕ) (a b : ℝ) (p : Piece) :
    Measurable fun t : ℝ => ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ *
      Real.exp (2 * n * potC σ ((Curve.ofPiece κ (rhoT n a b) p).ζ t / n)) := by
  have h1 : Measurable fun t : ℝ => ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ :=
    (measurable_ofPiece_w κ n a b p).norm
  have h2 : Measurable fun t : ℝ => potC σ (p.zeta t / (n : ℂ)) :=
    (CatalanCore.Decay.CurveFamily.measurable_potC σ).comp ((measurable_zeta p).div_const _)
  exact h1.mul (Real.measurable_exp.comp (measurable_const.mul h2))

/-- Integrability of the two integrands on a finite piece, from a uniform pointwise bound. -/
lemma integrable_finite_piece {σ : Measure ℂ} [IsFiniteMeasure σ] {bb A : ℝ}
    (hσ : BallMajA σ bb A (1 / 2)) (κ : ℂ) (n : ℕ) (a b : ℝ) (p : Piece) (hray : p.ray = false)
    {M : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ *
      Real.exp (2 * n * potC σ ((Curve.ofPiece κ (rhoT n a b) p).ζ t / n)) ≤ M) (k : ℕ) :
    Integrable (fun t : ℝ => ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ *
        Real.exp (2 * n * potC σ ((Curve.ofPiece κ (rhoT n a b) p).ζ t / n)))
      (Curve.ofPiece κ (rhoT n a b) p).ν ∧
    Integrable (fun t : ℝ => (Curve.ofPiece κ (rhoT n a b) p).w t *
        (Curve.ofPiece κ (rhoT n a b) p).ζ t ^ k) (Curve.ofPiece κ (rhoT n a b) p).ν := by
  have hν : (Curve.ofPiece κ (rhoT n a b) p).ν = volume.restrict (Ioc (0 : ℝ) 1) := by
    simp [Curve.ofPiece, Piece.nu, hray]
  rw [hν]
  refine ⟨integrable_Ioc_of_bdd (measurable_weightE σ κ n a b p).aestronglyMeasurable
    (M := M) (fun t ht => ?_), integrable_Ioc_of_bdd ?_ (M := M * Real.exp (4 * n * A) *
      (‖p.a‖ + ‖p.D‖) ^ k) (fun t ht => ?_)⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    exact hb t ht
  · exact ((measurable_ofPiece_w κ n a b p).mul
      ((measurable_zeta p).pow_const k)).aestronglyMeasurable
  · rw [norm_mul, norm_pow]
    have hw := norm_le_of_potC hσ n (p.zeta t / n) (norm_nonneg ((Curve.ofPiece κ (rhoT n a b) p).w t))
      (hb t ht)
    have hz : ‖p.zeta t‖ ≤ ‖p.a‖ + ‖p.D‖ := by
      unfold Piece.zeta
      calc ‖p.a + (t : ℂ) * p.D‖ ≤ ‖p.a‖ + ‖(t : ℂ) * p.D‖ := norm_add_le _ _
        _ = ‖p.a‖ + t * ‖p.D‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
        _ ≤ ‖p.a‖ + ‖p.D‖ := by nlinarith [ht.1, ht.2, norm_nonneg p.D]
    exact mul_le_mul hw (pow_le_pow_left₀ (norm_nonneg _) hz k) (by positivity)
      ((norm_nonneg _).trans hw)

/-- Integrability of the two integrands on the ray piece, from a decaying pointwise bound. -/
lemma integrable_ray_piece {σ : Measure ℂ} [IsFiniteMeasure σ] {bb A : ℝ}
    (hσ : BallMajA σ bb A (1 / 2)) (κ : ℂ) (n : ℕ) (a b : ℝ) (p : Piece) (hray : p.ray = true)
    {M μ : ℝ} (hμ : 0 < μ)
    (hb : ∀ t : ℝ, 0 < t → ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ *
      Real.exp (2 * n * potC σ ((Curve.ofPiece κ (rhoT n a b) p).ζ t / n)) ≤
        M * Real.exp (-μ * t)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ *
        Real.exp (2 * n * potC σ ((Curve.ofPiece κ (rhoT n a b) p).ζ t / n)))
      (Curve.ofPiece κ (rhoT n a b) p).ν ∧
    Integrable (fun t : ℝ => (Curve.ofPiece κ (rhoT n a b) p).w t *
        (Curve.ofPiece κ (rhoT n a b) p).ζ t ^ k) (Curve.ofPiece κ (rhoT n a b) p).ν := by
  have hν : (Curve.ofPiece κ (rhoT n a b) p).ν = volume.restrict (Ioi (0 : ℝ)) := by
    simp [Curve.ofPiece, Piece.nu, hray]
  rw [hν]
  obtain ⟨C, hC0, hC⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp k (half_pos hμ)
  refine ⟨integrable_Ioi_of_expb hμ (measurable_weightE σ κ n a b p).aestronglyMeasurable
    (M := M) (fun t ht => ?_), integrable_Ioi_of_expb (half_pos hμ) (M := M * Real.exp (4 * n * A) *
      ((‖p.a‖ + ‖p.D‖) ^ k * C)) ?_ (fun t ht => ?_)⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    exact hb t ht
  · exact ((measurable_ofPiece_w κ n a b p).mul
      ((measurable_zeta p).pow_const k)).aestronglyMeasurable
  · have ht0 : 0 < t := ht
    rw [norm_mul, norm_pow]
    have hw := norm_le_of_potC hσ n (p.zeta t / n) (norm_nonneg ((Curve.ofPiece κ (rhoT n a b) p).w t))
      (hb t ht0)
    have hz : ‖p.zeta t‖ ≤ (‖p.a‖ + ‖p.D‖) * (1 + t) := by
      unfold Piece.zeta
      calc ‖p.a + (t : ℂ) * p.D‖ ≤ ‖p.a‖ + ‖(t : ℂ) * p.D‖ := norm_add_le _ _
        _ = ‖p.a‖ + t * ‖p.D‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        _ ≤ (‖p.a‖ + ‖p.D‖) * (1 + t) := by
          nlinarith [norm_nonneg p.a, norm_nonneg p.D, mul_nonneg ht0.le (norm_nonneg p.a)]
    have hz2 : ‖p.zeta t‖ ^ k ≤ (‖p.a‖ + ‖p.D‖) ^ k * (C * Real.exp (μ / 2 * t)) := by
      calc ‖p.zeta t‖ ^ k ≤ ((‖p.a‖ + ‖p.D‖) * (1 + t)) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) hz k
        _ = (‖p.a‖ + ‖p.D‖) ^ k * (1 + t) ^ k := mul_pow _ _ _
        _ ≤ (‖p.a‖ + ‖p.D‖) ^ k * (C * Real.exp (μ / 2 * t)) :=
            mul_le_mul_of_nonneg_left (hC t ht0.le) (by positivity)
    have hw' : ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ ≤ M * Real.exp (-μ * t) * Real.exp (4 * n * A) :=
      norm_le_of_potC hσ n (p.zeta t / n) (norm_nonneg _) (hb t ht0)
    have hE : Real.exp (-μ * t) * Real.exp (μ / 2 * t) = Real.exp (-(μ / 2) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖(Curve.ofPiece κ (rhoT n a b) p).w t‖ * ‖(Curve.ofPiece κ (rhoT n a b) p).ζ t‖ ^ k
        ≤ (M * Real.exp (-μ * t) * Real.exp (4 * n * A)) *
          ((‖p.a‖ + ‖p.D‖) ^ k * (C * Real.exp (μ / 2 * t))) :=
          mul_le_mul hw' hz2 (by positivity) ((norm_nonneg _).trans hw')
      _ = M * Real.exp (4 * n * A) * ((‖p.a‖ + ‖p.D‖) ^ k * C) *
          (Real.exp (-μ * t) * Real.exp (μ / 2 * t)) := by ring
      _ = _ := by rw [hE]

/-! ### IV. Pointwise decay on the ray, and the per-piece facts -/

/-- The decaying pointwise bound of the weight integrand on a ray piece (the bound inside
`curveBd_ray`, with a constant that need not be uniform). -/
lemma ray_curveG_le (σ : Measure ℂ) (a b : ℝ) (hlam : 0 < 3 * |a| + |b|) {n : ℕ} (hn : 1 ≤ n)
    {ℓ δ R0 : ℝ} (hδ : 0 < δ) (hR0 : 0 ≤ R0) {p : Piece} (hD : ‖p.D‖ = 1)
    (hp : RayOK σ n ℓ δ R0 p) {κ : ℂ} (hκ : ‖κ‖ = (2 * Real.pi)⁻¹) :
    ∃ M : ℝ, ∀ t : ℝ, 0 < t →
      curveG σ n (Curve.ofPiece κ (rhoT n a b) p) t ≤ M * Real.exp (-(δ / 2) * t) := by
  obtain ⟨Cp, hCp0, hCp⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp 3
    (show 0 < δ / 2 by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + R0) ^ 3 * Cp *
    ((n : ℝ) ^ 4 * Real.exp (n * ℓ)), fun t ht0 => ?_⟩
  obtain ⟨hg, hW, hR⟩ := hp t ht0
  have h := curveG_pt_le σ a b hlam hn hκ hg
  rw [hD] at h
  set x : ℝ := ‖p.zeta t / (n : ℂ)‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have htn : t / n ≤ t := div_le_self ht0.le hn1
  have h1x : 1 + x ≤ (1 + R0) * (1 + t) := by nlinarith
  have hx3 : (1 + x) ^ 3 ≤ (1 + R0) ^ 3 * (1 + t) ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1x 3
  have hn4 : Real.exp (4 * Real.log n) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn0]
  have h3 : Real.exp (3 * Real.log (1 + x)) = (1 + x) ^ 3 := by
    rw [show (3 : ℝ) * Real.log (1 + x) = ((3 : ℕ) : ℝ) * Real.log (1 + x) by norm_num,
      Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hnW : (n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) ≤ n * ℓ - δ * t := by
    have := mul_le_mul_of_nonneg_left hW hn0.le
    have e : (n : ℝ) * (ℓ - δ * (t / n)) = n * ℓ - δ * t := by field_simp
    linarith
  have hE : Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ (p.zeta t / (n : ℂ)) +
      RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + x)) ≤
      Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) * (n : ℝ) ^ 4 * Real.exp (-δ * t) *
        ((1 + R0) ^ 3 * (1 + t) ^ 3) := by
    calc _ ≤ Real.exp ((n * ℓ - δ * t) + RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + x)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) * Real.exp (4 * Real.log n) *
            Real.exp (-δ * t) * Real.exp (3 * Real.log (1 + x)) := by
          simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
          rw [h3, hn4]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hx3
  have hpow := hCp t ht0.le
  have hexp : Real.exp (-δ * t) * Real.exp (δ / 2 * t) = Real.exp (-(δ / 2) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  calc curveG σ n (Curve.ofPiece κ (rhoT n a b) p) t
      ≤ 1 * (2 * Real.pi)⁻¹ * (laiKC * Real.exp ((n : ℝ) * wField 3 2 2 6 (2 * Real.pi) σ
          (p.zeta t / (n : ℂ)) + RConst 3 2 2 6 + 4 * Real.log n + 3 * Real.log (1 + x))) := h
    _ ≤ 1 * (2 * Real.pi)⁻¹ * (laiKC * (Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) *
          (n : ℝ) ^ 4 * Real.exp (-δ * t) * ((1 + R0) ^ 3 * (1 + t) ^ 3))) := by
        have := laiKC_nonneg
        gcongr
    _ ≤ 1 * (2 * Real.pi)⁻¹ * (laiKC * (Real.exp (n * ℓ) * Real.exp (RConst 3 2 2 6) *
          (n : ℝ) ^ 4 * Real.exp (-δ * t) * ((1 + R0) ^ 3 * (Cp * Real.exp (δ / 2 * t))))) := by
        have := laiKC_nonneg
        gcongr
    _ = _ := by rw [← hexp]; ring

/-- The per-piece hypothesis (the cell data of W2): a finite piece satisfies `PieceOK` with a
bounded constant, the ray satisfies `RayOK` with Lai's tail numbers. -/
def PieceGood (σ : Measure ℂ) (n : ℕ) (ℓ' Cfin : ℝ) (p : Piece) : Prop :=
  (p.ray = false → ∃ Rs : ℝ, PieceOK σ n ℓ' Rs p ∧
    ‖p.D‖ * (2 * Real.pi)⁻¹ * laiKC * Real.exp (RConst 3 2 2 6) * (1 + Rs) ^ 3 ≤ Cfin) ∧
  (p.ray = true → ‖p.D‖ = 1 ∧ RayOK σ n ℓ' (1 / 40) (27 / 5) p)

theorem PieceGood.conj {σ : Measure ℂ} (hσ : σ.map (starRingEnd ℂ) = σ) {n : ℕ} {ℓ' Cfin : ℝ}
    {p : Piece} (h : PieceGood σ n ℓ' Cfin p) : PieceGood σ n ℓ' Cfin p.conj := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨Rs, h1, h2⟩ := h.1 hr
    refine ⟨Rs, PieceOK.conj hσ h1, ?_⟩
    simpa [Piece.conj] using h2
  · obtain ⟨h1, h2⟩ := h.2 hr
    refine ⟨?_, RayOK.conj hσ h2⟩
    simpa [Piece.conj] using h1

lemma CurveBd.mono {σ : Measure ℂ} {n : ℕ} {c : Curve} {B B' : ℝ} (h : CurveBd σ n c B)
    (hB : B ≤ B') : CurveBd σ n c B' := ⟨h.1, h.2.trans hB⟩

/-- **Per-curve facts**: the `CurveBd` bound and the integrability of all moments. -/
theorem curve_good (σ : Measure ℂ) [IsFiniteMeasure σ] {bb A : ℝ} (hσ : BallMajA σ bb A (1 / 2))
    (a b : ℝ) (hlam : 0 < 3 * |a| + |b|) {n : ℕ} (hn : 1 ≤ n) {ℓ' Cfin Cr : ℝ}
    (hCr : ∀ p : Piece, p.ray = true → ‖p.D‖ = 1 → RayOK σ n ℓ' (1 / 40) (27 / 5) p →
      ∀ κ : ℂ, ‖κ‖ = (2 * Real.pi)⁻¹ →
      CurveBd σ n (Curve.ofPiece κ (rhoT n a b) p) (Cr * (n : ℝ) ^ 4 * Real.exp (n * ℓ')))
    {p : Piece} (hp : PieceGood σ n ℓ' Cfin p) {κ : ℂ} (hκ : ‖κ‖ = (2 * Real.pi)⁻¹) :
    CurveBd σ n (Curve.ofPiece κ (rhoT n a b) p)
        (max Cfin Cr * (n : ℝ) ^ 4 * Real.exp (n * ℓ')) ∧
      ∀ k : ℕ, Integrable (fun t : ℝ => (Curve.ofPiece κ (rhoT n a b) p).w t *
        (Curve.ofPiece κ (rhoT n a b) p).ζ t ^ k) (Curve.ofPiece κ (rhoT n a b) p).ν := by
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hE := (Real.exp_pos (n * ℓ')).le
  cases hray : p.ray
  · obtain ⟨Rs, hOK, hle⟩ := hp.1 hray
    refine ⟨(curveBd_seg σ a b hlam hn hray hOK hκ).mono ?_, fun k => ?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (hle.trans (le_max_left _ _)) hn4) hE
    · refine (integrable_finite_piece hσ κ n a b p hray (M := ‖p.D‖ * (2 * Real.pi)⁻¹ *
        EB n ℓ' Rs) (fun t ht => piece_pt_le σ a b hlam hn hOK hκ ht) k).2
  · obtain ⟨hD, hR⟩ := hp.2 hray
    refine ⟨(hCr p hray hD hR κ hκ).mono ?_, fun k => ?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hn4) hE
    · obtain ⟨M, hM⟩ := ray_curveG_le σ a b hlam hn (by norm_num : (0 : ℝ) < 1 / 40)
        (by norm_num : (0 : ℝ) ≤ 27 / 5) hD hR hκ
      exact (integrable_ray_piece hσ κ n a b p hray (M := M) (μ := 1 / 40 / 2) (by norm_num)
        (fun t ht => hM t ht) k).2

lemma chainPieces_length (a : ℂ) : ∀ l : List ℂ, (chainPieces (a :: l)).length = l.length
  | [] => by simp [chainPieces]
  | b :: rest => by
    simp only [chainPieces, List.length_cons]
    rw [chainPieces_length b rest]

lemma laiPieces_length (v : ℝ) (pts : List ℂ) (d : ℂ) :
    (laiPieces v pts d).length = pts.length + 1 := by
  unfold laiPieces polyPieces
  rw [List.length_append, chainPieces_length]
  simp

/-! ### V. LD09: `lai_decay_dual` -/

/-- **LD09, Theorem A for Lai's family (dual form).**  Let `σ` be a finite measure of mass `3`, carried
by a ball and with `σ(B(c, r)) ≤ A √r`, invariant under conjugation.  Suppose the atom field is
bounded (`ω(x) + 2 potC σ(-x) ≤ a*` on `[0, 6]`, `a* ≤ ℓ + ρ`) and, for every `η > 0` and all large `n`,
there is an admissible polygon `v → pts → ∞·i` (the `PieceGood` data: `PieceOK` on the finite pieces,
`RayOK` on the ray, both at `ℓ + η`) with a bounded number of pieces and bounded constants.
Then for every `ε > 0` there is `R₀` such that for all `n ≥ R₀`, all `(a, b)` with `λ = 3|a| + |b| > 0`
and all `|t| ≤ λ e^{-ρ n}`,
`|J_n(a, b, aζ(3) + bζ(4) + t)| ≤ λ^{3n} exp(-(D - ε) n²)`, `D = -(κ - energyC σ + 3 ℓ)`,
`κ = 27/2 - 9 log 3`, `-energyC σ = I(σ)`. -/
theorem lai_decay_dual {σ : Measure ℂ} [IsFiniteMeasure σ] {bb A : ℝ}
    (hσ : BallMajA σ bb A (1 / 2)) (hmass : σ.real univ = 3)
    (hconj : σ.map (starRingEnd ℂ) = σ) {ℓ ρ astar : ℝ} (hρ : astar ≤ ℓ + ρ)
    (hat : ∀ x ∈ Icc (0 : ℝ) 6, omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ astar)
    (hcont : ∀ η : ℝ, 0 < η → ∃ (N K : ℕ) (Cfin : ℝ), ∀ n : ℕ, N ≤ n → ∃ (v : ℝ) (pts : List ℂ),
      0 < v ∧ v < 2 * n + 1 ∧ (∀ m : ℤ, v ≠ m) ∧ (∀ z ∈ pts, 0 < z.im) ∧ pts.length ≤ K ∧
      ∀ p ∈ laiPieces v pts Complex.I, PieceGood σ n (ℓ + η) Cfin p) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ n : ℕ, R₀ ≤ n → ∀ a b t : ℝ, 0 < laiLam a b →
      |t| ≤ laiLam a b * Real.exp (-(ρ * n)) →
      |MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4 + t] (laiJ n)| ≤
        laiLam a b ^ (3 * n) * Real.exp (-(-((3 : ℝ) ^ 2 * (3 / 2 - Real.log 3) - energyC σ +
          3 * ℓ) - ε) * (n : ℝ) ^ 2) := by
  intro ε hε
  have hη : 0 < ε / 6 := by positivity
  obtain ⟨N, K, Cfin, hN⟩ := hcont (ε / 6) hη
  obtain ⟨Cr, hCr0, hCr⟩ := curveBd_ray (δ := 1 / 40) (R0 := 27 / 5) (by norm_num) (by norm_num)
  have hCmax0 : 0 ≤ max Cfin Cr := hCr0.trans (le_max_right _ _)
  set Cmax : ℝ := max Cfin Cr with hCmax
  set Ctot : ℝ := Cmax * (2 * ((K : ℝ) + 1)) + 7 * 6 with hCtot
  have hCtot0 : 0 < Ctot := by positivity
  obtain ⟨R1, hR1⟩ := CatalanCore.Decay.TheoremA.theoremA_eventually hσ hmass
    (by norm_num : (0 : ℝ) < 3) (ℓ + ε / 6) 4 (Real.log Ctot) (ε := ε / 2) (half_pos hε)
  refine ⟨max R1 (max N 1), fun n hn a b t hlam ht => ?_⟩
  have hnR : R1 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn1 : 1 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨v, pts, hv0, hv2, hvm, hpts, hlen, hP⟩ := hN n hnN
  have hd : 0 < (Complex.I).im := by simp
  set α : ℕ → ℂ := fun k => (((6 * t * (laiCoef n k : ℝ) / laiLam a b : ℝ)) : ℂ) with hα
  set Pcs : List Curve := (laiPieces v pts Complex.I).map (Curve.ofPiece (-kap) (rhoT n a b)) ++
    ((laiPieces v pts Complex.I).map Piece.conj).map (Curve.ofPiece kap (rhoT n a b)) with hPcs
  have hcs : laiCurves n a b t v pts Complex.I = Pcs ++ atomCurves n α := rfl
  have hCr' : ∀ p : Piece, p.ray = true → ‖p.D‖ = 1 → RayOK σ n (ℓ + ε / 6) (1 / 40) (27 / 5) p →
      ∀ κ : ℂ, ‖κ‖ = (2 * Real.pi)⁻¹ →
      CurveBd σ n (Curve.ofPiece κ (rhoT n a b) p)
        (Cr * (n : ℝ) ^ 4 * Real.exp (n * (ℓ + ε / 6))) :=
    fun p h1 h2 h3 κ hκ => hCr σ a b hlam n hn1 (ℓ + ε / 6) p h1 h2 h3 κ hκ
  have hgood : ∀ c ∈ Pcs, CurveBd σ n c (Cmax * (n : ℝ) ^ 4 * Real.exp (n * (ℓ + ε / 6))) ∧
      ∀ k : ℕ, Integrable (fun s : ℝ => c.w s * c.ζ s ^ k) c.ν := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact curve_good σ hσ a b hlam hn1 hCr' (hP p hp) norm_neg_kap
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact curve_good σ hσ a b hlam hn1 hCr' (PieceGood.conj hconj (hP p hp)) norm_kap
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
  have hW := lai_hW_exp σ hn1 (ℓ := ℓ + ε / 6) (astar := astar) (ρ := ρ) (q := 6) (by norm_num)
    (by linarith) hat α hα' Pcs (fun _ => Cmax) (fun c hc => (hgood c hc).1) hCtot0 hC
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

end CatalanCore.Lai.DecayDual

