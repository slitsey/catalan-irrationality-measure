module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Ray integrals of rational functions with real poles

`rayI x θ f = ∫_{r>0} f(x + r e^{iθ}) e^{iθ} dr`.  For `f = ∑ αᵢ/(z-pᵢ)` with `∑ αᵢ = 0` we compute `rayI` by
`Complex.log` primitives.
-/

open Complex MeasureTheory Filter Topology Set

namespace CatalanLambda.Decay

/-- Point on the ray from `x` in direction `θ`. -/
noncomputable def rayPt (x θ r : ℝ) : ℂ := (x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)

/-- Ray integral `∫_{r>0} f(x + r e^{iθ}) e^{iθ} dr`. -/
noncomputable def rayI (x θ : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), f (rayPt x θ r) * exp ((θ : ℂ) * I)

/-- Sign: `+1` if the pole is to the left of `x`, `-1` otherwise. -/
noncomputable def sg (x p : ℝ) : ℝ := if p < x then 1 else -1

lemma sg_mul_pos {x p : ℝ} (h : p ≠ x) : 0 < sg x p * (x - p) := by
  unfold sg
  split_ifs with h1
  · linarith
  · have : x < p := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h)
    linarith

lemma sg_ne_zero (x p : ℝ) : sg x p ≠ 0 := by
  unfold sg; split_ifs <;> norm_num

lemma rayPt_re (x θ r : ℝ) : (rayPt x θ r).re = x + r * Real.cos θ := by
  simp [rayPt, Complex.exp_ofReal_mul_I_re]

lemma rayPt_im (x θ r : ℝ) : (rayPt x θ r).im = r * Real.sin θ := by
  simp [rayPt, Complex.exp_ofReal_mul_I_im]

lemma ray_slit {x p θ r : ℝ} (hp : p ≠ x) (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ((sg x p : ℂ) * (rayPt x θ r - p)) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases hr.eq_or_lt with rfl | hr'
  · left
    have := sg_mul_pos hp
    simp [rayPt]
    linarith
  · right
    have h1 : ((sg x p : ℂ) * (rayPt x θ r - p)).im = sg x p * (r * Real.sin θ) := by
      simp [rayPt_im]
    rw [h1]
    exact mul_ne_zero (sg_ne_zero x p) (mul_ne_zero hr'.ne' hs)

lemma hasDerivAt_rayPt (x θ r : ℝ) :
    HasDerivAt (fun t : ℝ => rayPt x θ t) (exp ((θ : ℂ) * I)) r := by
  unfold rayPt
  simpa using ((hasDerivAt_id r).ofReal_comp.mul_const (exp ((θ : ℂ) * I))).const_add (x : ℂ)

lemma rayPt_sub_ne {x p θ r : ℝ} (hp : p ≠ x) (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    rayPt x θ r - p ≠ 0 := by
  intro h
  have := ray_slit hp hs hr
  rw [h] at this
  simp at this

lemma ray_hasDerivAt_log {x p θ : ℝ} (hp : p ≠ x) (hs : Real.sin θ ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun t : ℝ => log ((sg x p : ℂ) * (rayPt x θ t - p)))
      (exp ((θ : ℂ) * I) / (rayPt x θ r - p)) r := by
  have h1 : HasDerivAt (fun t : ℝ => (sg x p : ℂ) * (rayPt x θ t - p))
      ((sg x p : ℂ) * exp ((θ : ℂ) * I)) r :=
    ((hasDerivAt_rayPt x θ r).sub_const _).const_mul _
  have := h1.clog_real (ray_slit hp hs hr)
  convert this using 1
  have : (sg x p : ℂ) ≠ 0 := by exact_mod_cast sg_ne_zero x p
  have h2 := rayPt_sub_ne hp hs hr
  field_simp

lemma sg_exp_slit {x p θ : ℝ} (hs : Real.sin θ ≠ 0) :
    ((sg x p : ℂ) * exp ((θ : ℂ) * I)) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp [Complex.exp_ofReal_mul_I_im]
  exact ⟨sg_ne_zero x p, hs⟩

/-- Log-primitive evaluation of the ray integral of `∑ αᵢ/(z-pᵢ)` when `∑ αᵢ = 0`. -/
theorem rayI_logsum {ι : Type*} (s : Finset ι) (α : ι → ℂ) (p : ι → ℝ) (x θ : ℝ)
    (hα : ∑ i ∈ s, α i = 0) (hp : ∀ i ∈ s, p i ≠ x) (hs : Real.sin θ ≠ 0)
    (hint : IntegrableOn
      (fun r : ℝ => (∑ i ∈ s, α i / (rayPt x θ r - p i)) * exp ((θ : ℂ) * I)) (Ioi 0)) :
    rayI x θ (fun z => ∑ i ∈ s, α i / (z - p i))
      = ∑ i ∈ s, α i * (log ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I))
          - log ((sg x (p i) : ℂ) * ((x : ℂ) - p i))) := by
  set Φ : ℝ → ℂ := fun t => ∑ i ∈ s, α i * log ((sg x (p i) : ℂ) * (rayPt x θ t - p i)) with hΦ
  have hder : ∀ r ∈ Ici (0:ℝ),
      HasDerivAt Φ ((∑ i ∈ s, α i / (rayPt x θ r - p i)) * exp ((θ : ℂ) * I)) r := by
    intro r hr
    have := HasDerivAt.fun_sum (u := s)
      (fun i hi => (ray_hasDerivAt_log (hp i hi) hs hr).const_mul (α i))
    convert this using 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlim : Tendsto Φ atTop
      (𝓝 (∑ i ∈ s, α i * log ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I)))) := by
    have h1 : ∀ i ∈ s, Tendsto (fun r : ℝ => α i * log ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I)
          + (((sg x (p i) * (x - p i)) / r : ℝ) : ℂ))) atTop
        (𝓝 (α i * log ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I)))) := by
      intro i _
      have h0 : Tendsto (fun r : ℝ => (sg x (p i) * (x - p i)) / r) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h2 : Tendsto (fun r : ℝ => (((sg x (p i) * (x - p i)) / r : ℝ) : ℂ)) atTop (𝓝 0) := by
        have h5 := (Complex.continuous_ofReal.tendsto 0).comp h0
        rw [Complex.ofReal_zero] at h5
        exact h5
      have h3 : Tendsto (fun r : ℝ => (sg x (p i) : ℂ) * exp ((θ : ℂ) * I)
          + (((sg x (p i) * (x - p i)) / r : ℝ) : ℂ)) atTop
          (𝓝 ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I))) := by
        simpa using (tendsto_const_nhds (x := (sg x (p i) : ℂ) * exp ((θ : ℂ) * I))).add h2
      exact (h3.clog (sg_exp_slit hs)).const_mul _
    have h4 := tendsto_finsetSum s h1
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    simp only [hΦ]
    have hsum : ∑ i ∈ s, α i * log ((sg x (p i) : ℂ) * (rayPt x θ r - p i))
        = ∑ i ∈ s, α i * (((Real.log r : ℝ) : ℂ)
          + log ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I)
            + (((sg x (p i) * (x - p i)) / r : ℝ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hne : (sg x (p i) : ℂ) * exp ((θ : ℂ) * I)
            + (((sg x (p i) * (x - p i)) / r : ℝ) : ℂ) ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp [Complex.exp_ofReal_mul_I_im] at this
        rcases this with h | h
        · exact sg_ne_zero x (p i) (by exact_mod_cast h)
        · exact hs h
      have hrw : (sg x (p i) : ℂ) * (rayPt x θ r - p i)
          = (r : ℂ) * ((sg x (p i) : ℂ) * exp ((θ : ℂ) * I)
            + (((sg x (p i) * (x - p i)) / r : ℝ) : ℂ)) := by
        unfold rayPt
        have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
        push_cast
        field_simp
        ring
      rw [hrw, Complex.log_ofReal_mul hr hne]
    rw [hsum]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hα, zero_mul, zero_add]
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (hder 0 (Set.mem_Ici.2 le_rfl)).continuousAt.continuousWithinAt
    (fun r hr => hder r (Set.mem_Ici.2 (le_of_lt hr))) hint hlim
  unfold rayI
  rw [hmain]
  have h0 : Φ 0 = ∑ i ∈ s, α i * log ((sg x (p i) : ℂ) * ((x : ℂ) - p i)) := by
    simp [hΦ, rayPt]
  rw [h0, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ### Distance bounds along a ray -/

/-- The angular constant `(1 - |cos θ|)/2`. -/
noncomputable def kap2 (θ : ℝ) : ℝ := (1 - |Real.cos θ|) / 2

lemma kap2_pos {θ : ℝ} (hs : Real.sin θ ≠ 0) : 0 < kap2 θ := by
  unfold kap2
  have h1 : |Real.cos θ| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]
    have := Real.sin_sq_add_cos_sq θ
    have hp : 0 < Real.sin θ ^ 2 := by positivity
    nlinarith
  linarith

lemma norm_rayPt_sub_sq {x θ r : ℝ} (q : ℝ) (hr : 0 ≤ r) :
    kap2 θ * (|x - q| + r) ^ 2 ≤ ‖rayPt x θ r - q‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (rayPt x θ r - q).re = (x - q) + r * Real.cos θ := by
    simp [rayPt_re]; ring
  have him : (rayPt x θ r - q).im = r * Real.sin θ := by
    simp [rayPt_im]
  rw [hre, him]
  unfold kap2
  set d := x - q
  set c := Real.cos θ
  have hsc := Real.sin_sq_add_cos_sq θ
  have h1 : -(|d| * r * |c|) ≤ d * (r * c) := by
    have : |d * (r * c)| = |d| * r * |c| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr]; ring
    have := neg_abs_le (d * (r * c))
    linarith
  have hc0 := abs_nonneg c
  have hd2 : |d| ^ 2 = d ^ 2 := sq_abs d
  have hc2 : |c| ^ 2 = c ^ 2 := sq_abs c
  nlinarith [mul_nonneg (add_nonneg zero_le_one hc0) (sq_nonneg (|d| - r)), sq_abs d]

lemma norm_rayPt_sub_ge {x θ r : ℝ} (q : ℝ) (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    Real.sqrt (kap2 θ) * (|x - q| + r) ≤ ‖rayPt x θ r - q‖ := by
  have h := norm_rayPt_sub_sq (x := x) (θ := θ) q hr
  have hk := kap2_pos hs
  rw [← Real.sqrt_sq (norm_nonneg (rayPt x θ r - q))]
  calc Real.sqrt (kap2 θ) * (|x - q| + r)
      = Real.sqrt (kap2 θ * (|x - q| + r) ^ 2) := by
        rw [Real.sqrt_mul hk.le, Real.sqrt_sq (by positivity)]
    _ ≤ _ := Real.sqrt_le_sqrt h

lemma norm_inv_rayPt_le {x θ r : ℝ} (q : ℝ) (hq : q ≠ x) (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖(rayPt x θ r - q)⁻¹‖ ≤ 1 / (Real.sqrt (kap2 θ) * (|x - q| + r)) := by
  have hk := Real.sqrt_pos.2 (kap2_pos hs)
  have h := norm_rayPt_sub_ge (x := x) q hs hr
  rw [norm_inv]
  have hq0 : 0 < |x - q| := abs_pos.2 (sub_ne_zero.2 hq.symm)
  have hpos : 0 < Real.sqrt (kap2 θ) * (|x - q| + r) := by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h

lemma tendsto_norm_ray {x θ : ℝ} (q : ℝ) (hs : Real.sin θ ≠ 0) :
    Tendsto (fun r : ℝ => ‖rayPt x θ r - q‖) atTop atTop := by
  have hk := Real.sqrt_pos.2 (kap2_pos hs)
  have h1 : Tendsto (fun r : ℝ => Real.sqrt (kap2 θ) * (|x - q| + r)) atTop atTop :=
    (tendsto_atTop_add_const_left _ _ tendsto_id).const_mul_atTop hk
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact norm_rayPt_sub_ge q hs hr

lemma tendsto_inv_ray {x θ : ℝ} (q : ℝ) (hs : Real.sin θ ≠ 0) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun r : ℝ => ((rayPt x θ r - q) ^ n)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv, norm_pow]
  exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hn.ne').comp (tendsto_norm_ray q hs))

lemma integrableOn_invsq (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun r : ℝ => 1 / (m + r) ^ 2) (Ioi 0) := by
  have hd : ∀ r ∈ Ici (0:ℝ), HasDerivAt (fun r : ℝ => -(m + r)⁻¹) (1 / (m + r) ^ 2) r := by
    intro r hr
    have hne : m + r ≠ 0 := by have := Set.mem_Ici.1 hr; positivity
    have := (((hasDerivAt_id r).const_add m).inv hne).neg
    convert this using 1
    · funext t; simp
    · simp only [id, neg_div, neg_neg, one_div]
  refine integrableOn_Ioi_deriv_of_nonneg' hd (fun r _ => by positivity) (l := 0) ?_
  have : Tendsto (fun r : ℝ => m + r) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  simpa using (tendsto_inv_atTop_zero.comp this).neg

lemma integrableOn_of_bound {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {m C : ℝ} (hm : 0 < m) (h : ∀ r ∈ Ioi (0:ℝ), ‖g r‖ ≤ C * (1 / (m + r) ^ 2)) :
    IntegrableOn g (Ioi 0) :=
  Integrable.mono' ((integrableOn_invsq m hm).const_mul C) hg
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall h))

lemma norm_exp_ofReal_mul_I (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma integrableOn_ray2 {x θ : ℝ} (p a : ℝ) (hp : p ≠ x) (ha : a ≠ x) (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => ((rayPt x θ r - p)⁻¹ * (rayPt x θ r - a)⁻¹) * exp ((θ : ℂ) * I))
      (Ioi 0) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  have hp0 : 0 < |x - p| := abs_pos.2 (sub_ne_zero.2 hp.symm)
  have ha0 : 0 < |x - a| := abs_pos.2 (sub_ne_zero.2 ha.symm)
  set m := min |x - p| |x - a| with hm
  have hm0 : 0 < m := lt_min hp0 ha0
  refine integrableOn_of_bound (m := m) (C := 1 / K ^ 2) ?_ hm0 ?_
  · unfold rayPt
    exact (by fun_prop : Measurable fun r : ℝ =>
      ((((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - p)⁻¹ * (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - a)⁻¹)
        * exp ((θ : ℂ) * I)).aestronglyMeasurable
  · intro r hr
    have hr' : 0 ≤ r := le_of_lt hr
    rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_inv_rayPt_le (x := x) (θ := θ) p hp hs hr'
    have h2 := norm_inv_rayPt_le (x := x) (θ := θ) a ha hs hr'
    have hmp : m + r ≤ |x - p| + r := by have := min_le_left |x - p| |x - a|; linarith
    have hma : m + r ≤ |x - a| + r := by have := min_le_right |x - p| |x - a|; linarith
    have hmr : 0 < m + r := by linarith
    have h1' : 1 / (K * (|x - p| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have h2' : 1 / (K * (|x - a| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    calc ‖(rayPt x θ r - p)⁻¹‖ * ‖(rayPt x θ r - a)⁻¹‖
        ≤ (1 / (K * (m + r))) * (1 / (K * (m + r))) :=
          mul_le_mul (h1.trans h1') (h2.trans h2') (norm_nonneg _) (by positivity)
      _ = 1 / K ^ 2 * (1 / (m + r) ^ 2) := by field_simp

lemma integrableOn_ray3 {x θ : ℝ} (p a b : ℝ) (hp : p ≠ x) (ha : a ≠ x) (hb : b ≠ x)
    (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => ((rayPt x θ r - p)⁻¹ * (rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)
      * exp ((θ : ℂ) * I)) (Ioi 0) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  have hp0 : 0 < |x - p| := abs_pos.2 (sub_ne_zero.2 hp.symm)
  have ha0 : 0 < |x - a| := abs_pos.2 (sub_ne_zero.2 ha.symm)
  have hb0 : 0 < |x - b| := abs_pos.2 (sub_ne_zero.2 hb.symm)
  set m := min |x - p| (min |x - a| |x - b|) with hm
  have hm0 : 0 < m := lt_min hp0 (lt_min ha0 hb0)
  refine integrableOn_of_bound (m := m) (C := 1 / K ^ 3 * (1 / m)) ?_ hm0 ?_
  · unfold rayPt
    exact (by fun_prop : Measurable fun r : ℝ =>
      ((((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - p)⁻¹ * (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - a)⁻¹
        * (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - b)⁻¹)
        * exp ((θ : ℂ) * I)).aestronglyMeasurable
  · intro r hr
    have hr' : 0 ≤ r := le_of_lt hr
    rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_inv_rayPt_le (x := x) (θ := θ) p hp hs hr'
    have h2 := norm_inv_rayPt_le (x := x) (θ := θ) a ha hs hr'
    have h3 := norm_inv_rayPt_le (x := x) (θ := θ) b hb hs hr'
    have hmp : m + r ≤ |x - p| + r := by
      have := min_le_left |x - p| (min |x - a| |x - b|); linarith
    have hma : m + r ≤ |x - a| + r := by
      have := (min_le_right |x - p| (min |x - a| |x - b|)).trans (min_le_left |x - a| |x - b|)
      linarith
    have hmb : m + r ≤ |x - b| + r := by
      have := (min_le_right |x - p| (min |x - a| |x - b|)).trans (min_le_right |x - a| |x - b|)
      linarith
    have hmr : 0 < m + r := by linarith
    have h1' : 1 / (K * (|x - p| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have h2' : 1 / (K * (|x - a| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have h3' : 1 / (K * (|x - b| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    calc ‖(rayPt x θ r - p)⁻¹‖ * ‖(rayPt x θ r - a)⁻¹‖ * ‖(rayPt x θ r - b)⁻¹‖
        ≤ (1 / (K * (m + r))) * (1 / (K * (m + r))) * (1 / (K * (m + r))) :=
          mul_le_mul (mul_le_mul (h1.trans h1') (h2.trans h2') (norm_nonneg _) (by positivity))
            (h3.trans h3') (norm_nonneg _) (by positivity)
      _ = 1 / K ^ 3 * (1 / (m + r) ^ 3) := by field_simp
      _ ≤ 1 / K ^ 3 * (1 / m * (1 / (m + r) ^ 2)) := by
          gcongr
          rw [div_mul_div_comm, one_mul]
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith [sq_nonneg (m + r), hr']
      _ = 1 / K ^ 3 * (1 / m) * (1 / (m + r) ^ 2) := by ring

/-- Double pole: `∫_ray 1/(z-q)^2 = 1/(x-q)`, independent of the direction. -/
theorem rayI_pow2 {x θ : ℝ} (q : ℝ) (hq : q ≠ x) (hs : Real.sin θ ≠ 0) :
    rayI x θ (fun z => (z - q)⁻¹ * (z - q)⁻¹) = ((x : ℂ) - q)⁻¹ := by
  have hder : ∀ r ∈ Ici (0:ℝ), HasDerivAt (fun t : ℝ => -(rayPt x θ t - q)⁻¹)
      (((rayPt x θ r - q)⁻¹ * (rayPt x θ r - q)⁻¹) * exp ((θ : ℂ) * I)) r := by
    intro r hr
    have hne := rayPt_sub_ne hq hs (Set.mem_Ici.1 hr)
    have := (((hasDerivAt_rayPt x θ r).sub_const (q : ℂ)).inv hne).neg
    convert this using 1
    field_simp
  have hint := integrableOn_ray2 (x := x) (θ := θ) q q hq hq hs
  have hlim : Tendsto (fun t : ℝ => -(rayPt x θ t - q)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_ray (x := x) q hs 1 one_pos).neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (hder 0 (Set.mem_Ici.2 le_rfl)).continuousAt.continuousWithinAt
    (fun r hr => hder r (Set.mem_Ici.2 (le_of_lt hr))) hint hlim
  unfold rayI
  rw [hmain]
  simp [rayPt]

/-- Triple pole: `∫_ray 1/(z-q)^3 = 1/(2 (x-q)^2)`, independent of the direction. -/
theorem rayI_pow3 {x θ : ℝ} (q : ℝ) (hq : q ≠ x) (hs : Real.sin θ ≠ 0) :
    rayI x θ (fun z => (z - q)⁻¹ * (z - q)⁻¹ * (z - q)⁻¹) = (2 * ((x : ℂ) - q) ^ 2)⁻¹ := by
  have hder : ∀ r ∈ Ici (0:ℝ), HasDerivAt (fun t : ℝ => -(2 * (rayPt x θ t - q) ^ 2)⁻¹)
      (((rayPt x θ r - q)⁻¹ * (rayPt x θ r - q)⁻¹ * (rayPt x θ r - q)⁻¹) * exp ((θ : ℂ) * I)) r := by
    intro r hr
    have hne := rayPt_sub_ne hq hs (Set.mem_Ici.1 hr)
    have h1 := ((hasDerivAt_rayPt x θ r).sub_const (q : ℂ)).pow 2
    have h2 := ((h1.const_mul (2 : ℂ)).inv (mul_ne_zero two_ne_zero (pow_ne_zero 2 hne))).neg
    convert h2 using 1
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  have hint : IntegrableOn (fun r : ℝ => ((rayPt x θ r - q)⁻¹ * (rayPt x θ r - q)⁻¹
      * (rayPt x θ r - q)⁻¹) * exp ((θ : ℂ) * I)) (Ioi 0) :=
    integrableOn_ray3 (x := x) (θ := θ) q q q hq hq hq hs
  have hlim : Tendsto (fun t : ℝ => -(2 * (rayPt x θ t - q) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_ray (x := x) q hs 2 two_pos).const_mul (2⁻¹ : ℂ)
    have h' := h.neg
    simp only [mul_zero, neg_zero] at h'
    refine h'.congr (fun r => ?_)
    rw [mul_inv]
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (hder 0 (Set.mem_Ici.2 le_rfl)).continuousAt.continuousWithinAt
    (fun r hr => hder r (Set.mem_Ici.2 (le_of_lt hr))) hint hlim
  unfold rayI
  rw [hmain]
  simp [rayPt]

/-- `contL x φ f`: lower ray (outbound) minus upper ray (outbound), i.e. `∫_Γ f dz` for the contour `Γ`
traversed downward (upper ray inbound, lower ray outbound). -/
noncomputable def contL (x φ : ℝ) (f : ℂ → ℂ) : ℂ := rayI x (-φ) f - rayI x φ f

lemma log_exp_I {t : ℝ} (h1 : -Real.pi < t) (h2 : t ≤ Real.pi) :
    log (exp ((t : ℂ) * I)) = (t : ℂ) * I := by
  apply Complex.log_exp <;> simpa using ‹_›

lemma neg_exp_eq (t : ℝ) : -exp ((t : ℂ) * I) = exp (((t - Real.pi : ℝ) : ℂ) * I) := by
  have : exp (((t - Real.pi : ℝ) : ℂ) * I) = exp ((t : ℂ) * I) * exp (-((Real.pi : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp

lemma log_signs {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi) :
    log (exp (((-φ : ℝ) : ℂ) * I)) - log (exp ((φ : ℂ) * I)) = -(2 * φ : ℂ) * I ∧
    log (-exp (((-φ : ℝ) : ℂ) * I)) - log (-exp ((φ : ℂ) * I))
      = (2 * (Real.pi - φ) : ℂ) * I := by
  have hpi := Real.pi_pos
  constructor
  · rw [log_exp_I (by linarith) (by linarith), log_exp_I (by linarith) (by linarith)]
    push_cast; ring
  · have e1 : -exp (((-φ : ℝ) : ℂ) * I) = exp (((-φ + Real.pi : ℝ) : ℂ) * I) := by
      have := neg_exp_eq (-φ + Real.pi)
      rw [show -φ + Real.pi - Real.pi = -φ by ring] at this
      rw [← neg_neg (exp (((-φ + Real.pi : ℝ) : ℂ) * I)), ← this]
    rw [e1, neg_exp_eq φ, log_exp_I (by linarith) (by linarith), log_exp_I (by linarith) (by linarith)]
    push_cast; ring


theorem contL_logsum {ι : Type*} (s : Finset ι) (α : ι → ℂ) (p : ι → ℝ) (x φ : ℝ)
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hα : ∑ i ∈ s, α i = 0) (hp : ∀ i ∈ s, p i ≠ x)
    (hintU : IntegrableOn
      (fun r : ℝ => (∑ i ∈ s, α i / (rayPt x φ r - p i)) * exp ((φ : ℂ) * I)) (Ioi 0))
    (hintL : IntegrableOn
      (fun r : ℝ => (∑ i ∈ s, α i / (rayPt x (-φ) r - p i)) * exp (((-φ : ℝ) : ℂ) * I)) (Ioi 0)) :
    contL x φ (fun z => ∑ i ∈ s, α i / (z - p i))
      = -(2 * Real.pi * I) * ∑ i ∈ s, (if p i < x then α i else 0) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  unfold contL
  rw [rayI_logsum s α p x (-φ) hα hp hsφ' hintL, rayI_logsum s α p x φ hα hp hsφ hintU,
    ← Finset.sum_sub_distrib]
  obtain ⟨hA, hB⟩ := log_signs h1 h2
  have key : ∀ i ∈ s, α i * (log ((sg x (p i) : ℂ) * exp (((-φ : ℝ) : ℂ) * I))
          - log ((sg x (p i) : ℂ) * ((x : ℂ) - p i)))
        - α i * (log ((sg x (p i) : ℂ) * exp ((φ : ℂ) * I))
          - log ((sg x (p i) : ℂ) * ((x : ℂ) - p i)))
      = (2 * Real.pi * I - 2 * φ * I) * α i - 2 * Real.pi * I * (if p i < x then α i else 0) := by
    intro i _
    by_cases hlt : p i < x
    · have : (sg x (p i) : ℂ) = 1 := by simp [sg, hlt]
      rw [this, if_pos hlt]
      simp only [one_mul]
      have : α i * (log (exp (((-φ : ℝ) : ℂ) * I)) - log ((x : ℂ) - p i))
          - α i * (log (exp ((φ : ℂ) * I)) - log ((x : ℂ) - p i))
          = α i * (log (exp (((-φ : ℝ) : ℂ) * I)) - log (exp ((φ : ℂ) * I))) := by ring
      rw [this, hA]; ring
    · have : (sg x (p i) : ℂ) = -1 := by simp [sg, hlt]
      rw [this, if_neg hlt]
      simp only [neg_one_mul]
      have : α i * (log (-exp (((-φ : ℝ) : ℂ) * I)) - log (-((x : ℂ) - p i)))
          - α i * (log (-exp ((φ : ℂ) * I)) - log (-((x : ℂ) - p i)))
          = α i * (log (-exp (((-φ : ℝ) : ℂ) * I)) - log (-exp ((φ : ℂ) * I))) := by ring
      rw [this, hB]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, hα, ← Finset.mul_sum]
  ring


lemma rayI_congr {x θ : ℝ} {f g : ℂ → ℂ} (h : ∀ r : ℝ, 0 ≤ r → f (rayPt x θ r) = g (rayPt x θ r)) :
    rayI x θ f = rayI x θ g := by
  unfold rayI
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [h r (le_of_lt hr)]

/-- Three distinct simple poles. -/
theorem contL_S111 (u v w x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hu : u ≠ x) (hv : v ≠ x) (hw : w ≠ x) :
    contL x φ (fun z => (z - u)⁻¹ * (z - v)⁻¹ * (z - w)⁻¹)
      = -(2 * Real.pi * I) *
        ((if u < x then 1 / (((u : ℂ) - v) * ((u : ℂ) - w)) else 0)
        + (if v < x then 1 / (((v : ℂ) - u) * ((v : ℂ) - w)) else 0)
        + (if w < x then 1 / (((w : ℂ) - u) * ((w : ℂ) - v)) else 0)) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have cuv : (u : ℂ) - v ≠ 0 := sub_ne_zero.2 (by exact_mod_cast huv)
  have cuw : (u : ℂ) - w ≠ 0 := sub_ne_zero.2 (by exact_mod_cast huw)
  have cvw : (v : ℂ) - w ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hvw)
  have cvu : (v : ℂ) - u ≠ 0 := sub_ne_zero.2 (by exact_mod_cast huv.symm)
  have cwu : (w : ℂ) - u ≠ 0 := sub_ne_zero.2 (by exact_mod_cast huw.symm)
  have cwv : (w : ℂ) - v ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hvw.symm)
  set α : Fin 3 → ℂ := ![1 / (((u : ℂ) - v) * ((u : ℂ) - w)), 1 / (((v : ℂ) - u) * ((v : ℂ) - w)),
    1 / (((w : ℂ) - u) * ((w : ℂ) - v))] with hα
  set p : Fin 3 → ℝ := ![u, v, w] with hp
  have hrep : ∀ z : ℂ, z - u ≠ 0 → z - v ≠ 0 → z - w ≠ 0 →
      (z - u)⁻¹ * (z - v)⁻¹ * (z - w)⁻¹ = ∑ i : Fin 3, α i / (z - p i) := by
    intro z a b c
    simp only [Fin.sum_univ_three, hα, hp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have e1 : z - (u : ℂ) ≠ 0 := a
    field_simp
    ring
  have hsum0 : ∑ i : Fin 3, α i = 0 := by
    simp only [Fin.sum_univ_three, hα, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hpne : ∀ i ∈ (Finset.univ : Finset (Fin 3)), p i ≠ x := by
    intro i _
    fin_cases i <;> simp [hp, hu, hv, hw]
  have hcg : ∀ θ : ℝ, Real.sin θ ≠ 0 → ∀ r : ℝ, 0 ≤ r →
      (rayPt x θ r - u)⁻¹ * (rayPt x θ r - v)⁻¹ * (rayPt x θ r - w)⁻¹
        = ∑ i : Fin 3, α i / (rayPt x θ r - p i) := by
    intro θ hs r hr
    exact hrep _ (rayPt_sub_ne hu hs hr) (rayPt_sub_ne hv hs hr) (rayPt_sub_ne hw hs hr)
  have hint : ∀ θ : ℝ, Real.sin θ ≠ 0 → IntegrableOn
      (fun r : ℝ => (∑ i : Fin 3, α i / (rayPt x θ r - p i)) * exp ((θ : ℂ) * I)) (Ioi 0) := by
    intro θ hs
    refine (integrableOn_ray3 u v w hu hv hw hs).congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only [hcg θ hs r (le_of_lt hr)]
  have hc : contL x φ (fun z => (z - u)⁻¹ * (z - v)⁻¹ * (z - w)⁻¹)
      = contL x φ (fun z => ∑ i : Fin 3, α i / (z - p i)) := by
    unfold contL
    have hR : ∀ θ : ℝ, Real.sin θ ≠ 0 → rayI x θ (fun z => (z - u)⁻¹ * (z - v)⁻¹ * (z - w)⁻¹)
        = rayI x θ (fun z => ∑ i : Fin 3, α i / (z - p i)) :=
      fun θ hs => rayI_congr (fun r hr => hcg θ hs r hr)
    rw [hR (-φ) hsφ', hR φ hsφ]
  rw [hc, contL_logsum Finset.univ α p x φ h1 h2 (by simpa using hsum0) hpne (hint φ hsφ)
    (hint (-φ) hsφ')]
  simp only [Fin.sum_univ_three, hα, hp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rfl


lemma rayI_add_smul {x θ : ℝ} (f1 f2 : ℂ → ℂ) (c : ℂ)
    (h1 : IntegrableOn (fun r : ℝ => f1 (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0))
    (h2 : IntegrableOn (fun r : ℝ => f2 (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0)) :
    rayI x θ (fun z => f1 z + c * f2 z) = rayI x θ f1 + c * rayI x θ f2 := by
  unfold rayI
  rw [← integral_const_mul, ← integral_add h1 (h2.const_mul c)]
  congr 1
  funext r
  ring

/-- Double pole at `u` plus simple pole at `v`. -/
theorem contL_S21 (u v x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (huv : u ≠ v) (hu : u ≠ x) (hv : v ≠ x) :
    contL x φ (fun z => (z - u)⁻¹ * (z - u)⁻¹ * (z - v)⁻¹)
      = -(2 * Real.pi * I) *
        ((if v < x then 1 / (((v : ℂ) - u) ^ 2) else 0)
        - (if u < x then 1 / (((v : ℂ) - u) ^ 2) else 0)) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have cuv : (u : ℂ) - v ≠ 0 := sub_ne_zero.2 (by exact_mod_cast huv)
  have cvu : (v : ℂ) - u ≠ 0 := sub_ne_zero.2 (by exact_mod_cast huv.symm)
  set A : ℂ := 1 / (((v : ℂ) - u) ^ 2) with hA
  set C : ℂ := 1 / ((u : ℂ) - v) with hC
  set α : Fin 2 → ℂ := ![A, -A] with hα
  set p : Fin 2 → ℝ := ![v, u] with hp
  have hrep : ∀ z : ℂ, z - u ≠ 0 → z - v ≠ 0 →
      (z - u)⁻¹ * (z - u)⁻¹ * (z - v)⁻¹
        = (∑ i : Fin 2, α i / (z - p i)) + C * ((z - u)⁻¹ * (z - u)⁻¹) := by
    intro z a b
    simp only [Fin.sum_univ_two, hα, hp, hA, hC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    field_simp
    ring
  have hsum0 : ∑ i : Fin 2, α i = 0 := by
    simp [Fin.sum_univ_two, hα]
  have hpne : ∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ≠ x := by
    intro i _
    fin_cases i <;> simp [hp, hu, hv]
  have hcg : ∀ θ : ℝ, Real.sin θ ≠ 0 → ∀ r : ℝ, 0 ≤ r →
      (rayPt x θ r - u)⁻¹ * (rayPt x θ r - u)⁻¹ * (rayPt x θ r - v)⁻¹
        = (∑ i : Fin 2, α i / (rayPt x θ r - p i)) + C * ((rayPt x θ r - u)⁻¹ * (rayPt x θ r - u)⁻¹) := by
    intro θ hs r hr
    exact hrep _ (rayPt_sub_ne hu hs hr) (rayPt_sub_ne hv hs hr)
  have hpow : ∀ θ : ℝ, Real.sin θ ≠ 0 → IntegrableOn (fun r : ℝ =>
      ((rayPt x θ r - u)⁻¹ * (rayPt x θ r - u)⁻¹) * exp ((θ : ℂ) * I)) (Ioi 0) :=
    fun θ hs => integrableOn_ray2 u u hu hu hs
  have hint : ∀ θ : ℝ, Real.sin θ ≠ 0 → IntegrableOn
      (fun r : ℝ => (∑ i : Fin 2, α i / (rayPt x θ r - p i)) * exp ((θ : ℂ) * I)) (Ioi 0) := by
    intro θ hs
    have h3 := ((integrableOn_ray3 u u v hu hu hv hs).sub ((hpow θ hs).const_mul C))
    refine h3.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hcg θ hs r (le_of_lt hr)]
    ring
  have hR : ∀ θ : ℝ, Real.sin θ ≠ 0 →
      rayI x θ (fun z => (z - u)⁻¹ * (z - u)⁻¹ * (z - v)⁻¹)
        = rayI x θ (fun z => ∑ i : Fin 2, α i / (z - p i))
          + C * rayI x θ (fun z => (z - u)⁻¹ * (z - u)⁻¹) := by
    intro θ hs
    have hh := rayI_add_smul (x := x) (θ := θ) (fun z => ∑ i : Fin 2, α i / (z - p i))
      (fun z => (z - u)⁻¹ * (z - u)⁻¹) C (hint θ hs) (hpow θ hs)
    rw [← hh]
    exact rayI_congr (fun r hr => hcg θ hs r hr)
  have hc : contL x φ (fun z => (z - u)⁻¹ * (z - u)⁻¹ * (z - v)⁻¹)
      = contL x φ (fun z => ∑ i : Fin 2, α i / (z - p i)) := by
    unfold contL
    rw [hR (-φ) hsφ', hR φ hsφ, rayI_pow2 u hu hsφ', rayI_pow2 u hu hsφ]
    ring
  rw [hc, contL_logsum Finset.univ α p x φ h1 h2 (by simpa using hsum0) hpne (hint φ hsφ)
    (hint (-φ) hsφ')]
  simp only [Fin.sum_univ_two, hα, hp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  by_cases hvx : v < x <;> by_cases hux : u < x <;> simp [hvx, hux, hA]

/-- Triple pole: contributes nothing. -/
theorem contL_S3 (u x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi) (hu : u ≠ x) :
    contL x φ (fun z => (z - u)⁻¹ * (z - u)⁻¹ * (z - u)⁻¹) = 0 := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  unfold contL
  rw [rayI_pow3 u hu hsφ, rayI_pow3 u hu hsφ']
  ring


/-- One pole to the left of `x`, the other two (possibly equal) to the right. -/
theorem contL_tri_west (p a b x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p < x) (ha : x < a) (hb : x < b) :
    contL x φ (fun z => (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹)
      = -(2 * Real.pi * I) * (1 / (((p : ℂ) - a) * ((p : ℂ) - b))) := by
  by_cases hab : a = b
  · subst hab
    have hf : (fun z : ℂ => (z - p)⁻¹ * (z - a)⁻¹ * (z - a)⁻¹)
        = fun z : ℂ => (z - a)⁻¹ * (z - a)⁻¹ * (z - p)⁻¹ := by funext z; ring
    rw [hf, contL_S21 a p x φ h1 h2 (by linarith) (by linarith) (by linarith)]
    simp [hp, not_lt.2 ha.le, sq]
  · rw [contL_S111 p a b x φ h1 h2 (by linarith) (by linarith) hab (by linarith) (by linarith)
      (by linarith)]
    simp [hp, not_lt.2 ha.le, not_lt.2 hb.le]

/-- All three poles to the right of `x`: the contour integral vanishes. -/
theorem contL_tri_east (p a b x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : x < p) (ha : x < a) (hb : x < b) :
    contL x φ (fun z => (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹) = 0 := by
  have np := not_lt.2 hp.le
  have na := not_lt.2 ha.le
  have nb := not_lt.2 hb.le
  by_cases hab : a = b
  · subst hab
    by_cases hpa : p = a
    · subst hpa
      exact contL_S3 p x φ h1 h2 (by linarith)
    · have hf : (fun z : ℂ => (z - p)⁻¹ * (z - a)⁻¹ * (z - a)⁻¹)
          = fun z : ℂ => (z - a)⁻¹ * (z - a)⁻¹ * (z - p)⁻¹ := by funext z; ring
      rw [hf, contL_S21 a p x φ h1 h2 (Ne.symm hpa) (by linarith) (by linarith)]
      simp [np, na]
  · by_cases hpa : p = a
    · subst hpa
      rw [contL_S21 p b x φ h1 h2 hab (by linarith) (by linarith)]
      simp [np, nb]
    · by_cases hpb : p = b
      · subst hpb
        have hf : (fun z : ℂ => (z - p)⁻¹ * (z - a)⁻¹ * (z - p)⁻¹)
            = fun z : ℂ => (z - p)⁻¹ * (z - p)⁻¹ * (z - a)⁻¹ := by funext z; ring
        rw [hf, contL_S21 p a x φ h1 h2 hpa (by linarith) (by linarith)]
        simp [np, na]
      · rw [contL_S111 p a b x φ h1 h2 hpa hpb hab (by linarith) (by linarith) (by linarith)]
        simp [np, na, nb]

end CatalanLambda.Decay
