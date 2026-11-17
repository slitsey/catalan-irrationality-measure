module

public import CatalanCore.Decay.ComplexTaylor

@[expose] public section

/-!
# Wedge bounds: conjugation symmetry (W5), the tail on a vertical ray (W7 = Lemma T), the atom
bound (W6), and the cross-energy cell integral (W4) (Lai decay, LD14, LD15, LD16, LD17, LD08)

All statements are generic in the design `(e, r, B, K, θ)`, the dual measure `σ` and the ray
abscissa `x₁`.

* **W5** (`vField_conj`, `logPotC_conj`, `wField_conj`): `W_σ(s̄) = W_σ(s)` for conjugation-invariant `σ`.
* **Lemma T / W7** (`neg_two_logPotC_le`, `hasDerivAt_vField_ray`, `pi_div_two_sub_arg_le`,
  `ray_deriv_le`, `tail_antitone`, `tail_wField_le`): on `x₁ + i y`, `y ≥ y₁`, `W_σ ≤ g(y₁)` as soon as
  `(e+r) x₁/y₁ - θ + 2 σ(ℂ)/(y₁ + R₀) ≤ 0`.
* **W6** (`quad_majorant`, `quad_majorant_Icc`, `quad_sup_le`, `omegaF`, `omega_majorant`,
  `atom_quad_bound`, `atom_sup_le`): the atom function `ω(x) - 2U^σ(-x)` is bounded on `[0, K']` by its
  value at one point plus `A²/(2m)`.
* **W4** (`integral_abs_pow5`, `cell_integral_le`, `partition_integral_le`): the Taylor integral of an
  order-5 cell and its sum over an exact partition.
-/

namespace CatalanCore.Decay.WedgeBounds

open Complex Set MeasureTheory Filter Topology CatalanCore.Tools.Joukowski
  CatalanCore.Decay.ComplexTaylor CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
  Nat

noncomputable section

/-! ### W5: conjugation symmetry -/

theorem vField_conj (e r B K θ : ℝ) (s : ℂ) :
    vField e r B K θ (starRingEnd ℂ s) = vField e r B K θ s := by
  unfold vField
  have h1 : ∀ x : ℝ, ‖starRingEnd ℂ s - (x : ℂ)‖ = ‖s - (x : ℂ)‖ := fun x => by
    rw [← Complex.norm_conj (s - x)]; simp
  have h2 : ∀ x : ℝ, ‖starRingEnd ℂ s + (x : ℂ)‖ = ‖s + (x : ℂ)‖ := fun x => by
    rw [← Complex.norm_conj (s + x)]; simp
  simp only [h1, h2, Complex.conj_im, abs_neg]

theorem logPotC_conj {σ : Measure ℂ} (hσ : σ.map (starRingEnd ℂ) = σ) (s : ℂ) :
    logPotC σ (starRingEnd ℂ s) = logPotC σ s := by
  unfold logPotC
  congr 1
  have hm : MeasurableEmbedding (starRingEnd ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  calc ∫ u, Real.log ‖starRingEnd ℂ s - u‖ ∂σ
      = ∫ u, Real.log ‖starRingEnd ℂ s - u‖ ∂(σ.map (starRingEnd ℂ)) := by rw [hσ]
    _ = ∫ u, Real.log ‖starRingEnd ℂ s - starRingEnd ℂ u‖ ∂σ := hm.integral_map _
    _ = ∫ u, Real.log ‖s - u‖ ∂σ := by
        congr 1; funext u; rw [← map_sub, Complex.norm_conj]

/-- The decay field `W_σ = V - 2 U^σ`. -/
def wField (e r B K θ : ℝ) (σ : Measure ℂ) (s : ℂ) : ℝ :=
  vField e r B K θ s - 2 * logPotC σ s

/-- **W5 (LD15)**: `W_σ(s̄) = W_σ(s)` for a conjugation-invariant `σ`. -/
theorem wField_conj (e r B K θ : ℝ) {σ : Measure ℂ} (hσ : σ.map (starRingEnd ℂ) = σ) (s : ℂ) :
    wField e r B K θ σ (starRingEnd ℂ s) = wField e r B K θ σ s := by
  unfold wField
  rw [vField_conj, logPotC_conj hσ]

/-! ### W7 / Lemma T: the tail on a vertical ray -/

/-- `-2 U^σ(s) ≤ 2 σ(ℂ) log (y + R₀)` when `σ` lives in the disc `|x₁ - u| ≤ R₀` and
`|s - x₁| ≤ y`. -/
theorem neg_two_logPotC_le {σ : Measure ℂ} [IsFiniteMeasure σ] {x₁ R₀ y : ℝ} {s : ℂ}
    (hsupp : ∀ᵐ u ∂σ, ‖(x₁ : ℂ) - u‖ ≤ R₀) (hy : ‖s - x₁‖ ≤ y) (h1 : 1 ≤ y + R₀)
    (hint : Integrable (fun u => Real.log ‖s - u‖) σ) :
    -(2 * logPotC σ s) ≤ 2 * σ.real univ * Real.log (y + R₀) := by
  unfold logPotC
  have hae : ∀ᵐ u ∂σ, Real.log ‖s - u‖ ≤ Real.log (y + R₀) := by
    filter_upwards [hsupp] with u hu
    have hle : ‖s - u‖ ≤ y + R₀ := by
      calc ‖s - u‖ = ‖(s - x₁) + ((x₁ : ℂ) - u)‖ := by ring_nf
        _ ≤ ‖s - x₁‖ + ‖(x₁ : ℂ) - u‖ := norm_add_le _ _
        _ ≤ y + R₀ := add_le_add hy hu
    rcases (norm_nonneg (s - u)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]; exact Real.log_nonneg h1
    · exact Real.log_le_log hpos hle
  have := integral_mono_ae hint (integrable_const (Real.log (y + R₀))) hae
  rw [integral_const, smul_eq_mul] at this
  linarith

/-- The derivative of `V` along the ray `x₁ + i y`, `y > 0`. -/
theorem hasDerivAt_vField_ray (e r B K θ x₁ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => vField e r B K θ ((x₁ : ℂ) + t * I))
      ((psiTower e r B K θ 1 ((x₁ : ℂ) + y * I) * I).re) y := by
  have hs : ∀ t : ℝ, 0 < t → 0 < ((x₁ : ℂ) + t * I).im := fun t ht => by simpa using ht
  have hγ : HasDerivAt (fun t : ℝ => (x₁ : ℂ) + (t : ℂ) * I) I y := by
    have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x₁ : ℂ)
    simpa using this
  have h1 := (hasDerivAt_psiT e r B K θ (psiDom_of_im_pos B K (hs y hy))).scomp y hγ
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h1
  have h3 := h2.const_add (r * (K * Real.log K - K) - e * (B * Real.log B - B))
  have hev : (fun t : ℝ => vField e r B K θ ((x₁ : ℂ) + t * I)) =ᶠ[𝓝 y]
      fun t : ℝ => (r * (K * Real.log K - K) - e * (B * Real.log B - B)) +
        (Complex.reCLM ∘ fun t : ℝ => psiT e r B K θ ((x₁ : ℂ) + t * I)) t := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    simpa using vField_eq_psi e r B K θ (hs t ht)
  refine (h3.congr_of_eventuallyEq hev).congr_deriv ?_
  simp [mul_comm]

/-- `π/2 - arg s ≤ x₁ / y` for `s = x₁ + i y`, `x₁, y > 0`. -/
theorem pi_div_two_sub_arg_le {x₁ y : ℝ} (hx : 0 < x₁) (hy : 0 < y) :
    Real.pi / 2 - Complex.arg ((x₁ : ℂ) + y * I) ≤ x₁ / y := by
  set s : ℂ := (x₁ : ℂ) + y * I with hs
  have hre : s.re = x₁ := by simp [hs]
  have him : s.im = y := by simp [hs]
  have h1 : Complex.arg s < Real.pi / 2 := by
    have := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hx)))
    exact (abs_lt.mp this).2
  have h2 : 0 < Complex.arg s := by
    rcases (Complex.arg_nonneg_iff.mpr (by rw [him]; exact hy.le)).eq_or_lt with h0 | h0
    · exfalso
      have := Complex.arg_eq_zero_iff.mp h0.symm
      have hz : 0 ≤ s.re ∧ s.im = 0 := this
      rw [him] at hz; exact hy.ne' hz.2
    · exact h0
  have hb0 : 0 < Real.pi / 2 - Complex.arg s := by linarith
  have hb1 : Real.pi / 2 - Complex.arg s < Real.pi / 2 := by linarith
  have ht := Real.lt_tan hb0 hb1
  rw [Real.tan_pi_div_two_sub, Complex.tan_arg, hre, him, inv_div] at ht
  exact ht.le

/-- The upper bound for the derivative of `V` along the ray `x₁ + i y`, `x₁ > B ≥ 0`, `K ≥ 0`. -/
theorem ray_deriv_le (e r B K θ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {x₁ y : ℝ} (hx : B < x₁) (hy : 0 < y) :
    (psiTower e r B K θ 1 ((x₁ : ℂ) + y * I) * I).re ≤ (e + r) * x₁ / y - θ := by
  set s : ℂ := (x₁ : ℂ) + y * I with hs
  have hre : s.re = x₁ := by simp [hs]
  have him : s.im = y := by simp [hs]
  have hx0 : 0 < x₁ := lt_of_le_of_lt hB hx
  have a1 := pi_div_two_sub_arg_le hx0 hy
  have a3 : Complex.arg (s + K) < Real.pi / 2 := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [hre]; linarith) :
      0 < (s + K).re ∨ s + K = 0)
    exact (abs_lt.mp this).2
  have hsB : s - B = -((B : ℂ) - s) := by ring
  have a2 : Complex.arg ((B : ℂ) - s) < -(Real.pi / 2) := by
    have hi : 0 < (s - B).im := by simp [him, hy]
    have h1 : Complex.arg (-(s - B)) = Complex.arg (s - B) - Real.pi :=
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi
    have h2 : Complex.arg (s - B) < Real.pi / 2 := by
      have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [hre]; linarith) :
        0 < (s - B).re ∨ s - B = 0)
      exact (abs_lt.mp this).2
    have h3 : (B : ℂ) - s = -(s - B) := by ring
    rw [h3, h1]; linarith
  have hIm : (psiTower e r B K θ 1 s).im = (e + r) * Complex.arg s - e * Complex.arg ((B : ℂ) - s)
      - r * Complex.arg (s + K) + (θ - e * Real.pi) := by
    simp [psiTower, Complex.log_im, Complex.mul_im]
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, hIm]
  simp only [mul_zero, mul_one, zero_sub, sub_zero]
  have hxy : (e + r) * (Real.pi / 2 - Complex.arg s) ≤ (e + r) * (x₁ / y) :=
    mul_le_mul_of_nonneg_left a1 (add_nonneg he hr)
  have e2 : e * Complex.arg ((B : ℂ) - s) ≤ e * (-(Real.pi / 2)) :=
    mul_le_mul_of_nonneg_left a2.le he
  have e3 : r * Complex.arg (s + K) ≤ r * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left a3.le hr
  have : (e + r) * x₁ / y = (e + r) * (x₁ / y) := by ring
  rw [this]
  nlinarith

/-- **Lemma T (W7 / LD08, LD17), monotone part.**  Along the ray `x₁ + i y` (`x₁ > B`), the function
`g(y) = V(x₁ + i y) + 2 m log (y + R₀)` is non-increasing on `[y₁, ∞)` as soon as its derivative
bound is non-positive at `y₁`. -/
theorem tail_antitone (e r B K θ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {x₁ y₁ m R₀ : ℝ} (hx : B < x₁) (hy₁ : 0 < y₁) (hR : 0 ≤ R₀) (hm : 0 ≤ m)
    (hneg : (e + r) * x₁ / y₁ - θ + 2 * m / (y₁ + R₀) ≤ 0) {y : ℝ} (hy : y₁ ≤ y) :
    vField e r B K θ ((x₁ : ℂ) + y * I) + 2 * m * Real.log (y + R₀) ≤
      vField e r B K θ ((x₁ : ℂ) + y₁ * I) + 2 * m * Real.log (y₁ + R₀) := by
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun t : ℝ => vField e r B K θ ((x₁ : ℂ) + t * I) + 2 * m * Real.log (t + R₀))
      ((psiTower e r B K θ 1 ((x₁ : ℂ) + t * I) * I).re + 2 * m / (t + R₀)) t := by
    intro t ht
    have h1 := hasDerivAt_vField_ray e r B K θ x₁ ht
    have htR : t + R₀ ≠ 0 := by
      have : 0 < t + R₀ := by linarith
      exact this.ne'
    have h2 : HasDerivAt (fun t : ℝ => Real.log (t + R₀)) (1 / (t + R₀)) t := by
      have := ((hasDerivAt_id t).add_const R₀).log htR
      simpa using this
    have h3 := h1.add (h2.const_mul (2 * m))
    refine h3.congr_deriv ?_
    ring
  have hanti : AntitoneOn
      (fun t : ℝ => vField e r B K θ ((x₁ : ℂ) + t * I) + 2 * m * Real.log (t + R₀))
      (Ici y₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici y₁) ?_ ?_ ?_
    · intro t ht
      exact (hderiv t (lt_of_lt_of_le hy₁ ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hderiv t (lt_trans hy₁ ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := lt_trans hy₁ ht
      rw [(hderiv t ht0).deriv]
      have h1 := ray_deriv_le e r B K θ he hr hB hK hx ht0
      have h2 : (e + r) * x₁ / t ≤ (e + r) * x₁ / y₁ := by
        apply div_le_div_of_nonneg_left (mul_nonneg (add_nonneg he hr) (hB.trans hx.le))
          hy₁ ht.le
      have h3 : 2 * m / (t + R₀) ≤ 2 * m / (y₁ + R₀) := by
        apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by have := mem_Ioi.mp ht; linarith)
      linarith
  exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy

/-- **Lemma T, assembled (LD08, LD17).**  For `σ` finite, carried by `{|x₁ - u| ≤ R₀}`, with
`1 ≤ y₁ + R₀`, and every `y ≥ y₁`: `W_σ(x₁ + i y) ≤ g(y₁)`. -/
theorem tail_wField_le (e r B K θ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {σ : Measure ℂ} [IsFiniteMeasure σ] {x₁ y₁ R₀ : ℝ} (hx : B < x₁) (hy₁ : 0 < y₁)
    (hR : 0 ≤ R₀) (h1 : 1 ≤ y₁ + R₀)
    (hsupp : ∀ᵐ u ∂σ, ‖(x₁ : ℂ) - u‖ ≤ R₀)
    (hint : ∀ y : ℝ, y₁ ≤ y → Integrable (fun u => Real.log ‖((x₁ : ℂ) + y * I) - u‖) σ)
    (hneg : (e + r) * x₁ / y₁ - θ + 2 * σ.real univ / (y₁ + R₀) ≤ 0) {y : ℝ} (hy : y₁ ≤ y) :
    wField e r B K θ σ ((x₁ : ℂ) + y * I) ≤
      vField e r B K θ ((x₁ : ℂ) + y₁ * I) + 2 * σ.real univ * Real.log (y₁ + R₀) := by
  have hm : 0 ≤ σ.real univ := measureReal_nonneg
  have hnorm : ‖((x₁ : ℂ) + y * I) - x₁‖ ≤ y := by
    have hy0 : 0 ≤ y := hy₁.le.trans hy
    simp [abs_of_nonneg hy0]
  have h1y : 1 ≤ y + R₀ := by linarith
  have h2 := neg_two_logPotC_le hsupp hnorm h1y (hint y hy)
  have h3 := tail_antitone e r B K θ he hr hB hK hx hy₁ hR hm hneg hy
  unfold wField
  linarith

/-! ### W6: atoms by strong concavity (LD16) -/

/-- A second-derivative bound gives a quadratic majorant (open interval). -/
theorem quad_majorant {f f' f'' : ℝ → ℝ} {a b M xs : ℝ}
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Ioo a b, f'' x ≤ -M) (hxs : xs ∈ Ioo a b) :
    ∀ x ∈ Ioo a b, f x ≤ f xs + f' xs * (x - xs) - M / 2 * (x - xs) ^ 2 := by
  have hder' : ∀ x ∈ Ioo a b,
      HasDerivAt (fun x => f' x - f' xs + M * (x - xs)) (f'' x + M) x := fun x hx => by
    have := ((hf' x hx).sub_const (f' xs)).add (((hasDerivAt_id x).sub_const xs).const_mul M)
    refine this.congr_deriv ?_
    simp
  have hanti : AntitoneOn (fun x => f' x - f' xs + M * (x - xs)) (Ioo a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo a b) ?_ ?_ ?_
    · intro x hx; exact (hder' x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (hder' x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hder' x hx).deriv]
      linarith [hM x hx]
  have hh : ∀ t ∈ Ioo a b, HasDerivAt
      (fun x => f x - f xs - f' xs * (x - xs) + M / 2 * (x - xs) ^ 2)
      (f' t - f' xs + M * (t - xs)) t := fun t ht => by
    have h1 := ((hf t ht).sub_const (f xs)).sub
      (((hasDerivAt_id t).sub_const xs).const_mul (f' xs))
    have h2 := (((hasDerivAt_id t).sub_const xs).pow 2).const_mul (M / 2)
    refine (h1.add h2).congr_deriv ?_
    simp
    ring
  intro x hx
  rcases le_total x xs with hle | hle
  · have hsub : Icc x xs ⊆ Ioo a b := fun t ht => ⟨by linarith [hx.1, ht.1], by linarith [hxs.2, ht.2]⟩
    have hmono : MonotoneOn (fun x => f x - f xs - f' xs * (x - xs) + M / 2 * (x - xs) ^ 2)
        (Icc x xs) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc x xs) ?_ ?_ ?_
      · intro t ht; exact (hh t (hsub ht)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hh t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hh t (hsub (Ioo_subset_Icc_self ht))).deriv]
        have := hanti (hsub (Ioo_subset_Icc_self ht)) hxs ht.2.le
        simp only [sub_self, mul_zero, add_zero, sub_add_cancel] at this
        linarith
    have := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    simp only at this
    have h0' : f xs - f xs - f' xs * (xs - xs) + M / 2 * (xs - xs) ^ 2 = 0 := by ring
    linarith
  · have hsub : Icc xs x ⊆ Ioo a b := fun t ht => ⟨by linarith [hxs.1, ht.1], by linarith [hx.2, ht.2]⟩
    have hanti2 : AntitoneOn (fun x => f x - f xs - f' xs * (x - xs) + M / 2 * (x - xs) ^ 2)
        (Icc xs x) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc xs x) ?_ ?_ ?_
      · intro t ht; exact (hh t (hsub ht)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hh t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hh t (hsub (Ioo_subset_Icc_self ht))).deriv]
        have := hanti hxs (hsub (Ioo_subset_Icc_self ht)) ht.1.le
        simp only [sub_self, mul_zero, add_zero, sub_add_cancel] at this
        linarith
    have := hanti2 ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    simp only at this
    have h0' : f xs - f xs - f' xs * (xs - xs) + M / 2 * (xs - xs) ^ 2 = 0 := by ring
    linarith

/-- The same on the closed interval, for `f` continuous there. -/
theorem quad_majorant_Icc {f f' f'' : ℝ → ℝ} {a b M xs : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Ioo a b, f'' x ≤ -M) (hxs : xs ∈ Ioo a b) (hc : ContinuousOn f (Icc a b)) :
    ∀ x ∈ Icc a b, f x ≤ f xs + f' xs * (x - xs) - M / 2 * (x - xs) ^ 2 := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have := le_on_closure (f := f) (g := fun x => f xs + f' xs * (x - xs) - M / 2 * (x - xs) ^ 2)
    (s := Ioo a b) (quad_majorant hf hf' hM hxs) (by rw [hcl]; exact hc)
    (by rw [hcl]; fun_prop)
  intro x hx
  exact this (by rw [hcl]; exact hx)

/-- The sup bound from a quadratic majorant with `m > 0`. -/
theorem quad_sup_le {a xs A m : ℝ} (hm : 0 < m) {S : Set ℝ} {f : ℝ → ℝ}
    (h : ∀ x ∈ S, f x ≤ a + A * (x - xs) - m / 2 * (x - xs) ^ 2) :
    ∀ x ∈ S, f x ≤ a + A ^ 2 / (2 * m) := by
  intro x hx
  have := h x hx
  have h2 : A * (x - xs) - m / 2 * (x - xs) ^ 2 ≤ A ^ 2 / (2 * m) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (A - m * (x - xs))]
  linarith

/-- `log |x + u|` as a function of `x`: first and second derivatives. -/
def ln1 (u : ℂ) (x : ℝ) : ℝ := (x + u.re) / ((x + u.re) ^ 2 + u.im ^ 2)

def ln2 (u : ℂ) (x : ℝ) : ℝ := (u.im ^ 2 - (x + u.re) ^ 2) / ((x + u.re) ^ 2 + u.im ^ 2) ^ 2

theorem logNorm_eq (u : ℂ) (x : ℝ) :
    Real.log ‖(x : ℂ) + u‖ = Real.log ((x + u.re) ^ 2 + u.im ^ 2) / 2 := by
  have h : ‖(x : ℂ) + u‖ ^ 2 = (x + u.re) ^ 2 + u.im ^ 2 := by
    rw [sq_norm_eq]; simp
  rw [← h, Real.log_pow]
  push_cast
  ring

theorem hasDerivAt_logNorm (u : ℂ) {x : ℝ} (hv : 0 < x + u.re) :
    HasDerivAt (fun x : ℝ => Real.log ‖(x : ℂ) + u‖) (ln1 u x) x := by
  have hne : (x + u.re) ^ 2 + u.im ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => (x + u.re) ^ 2 + u.im ^ 2) (2 * (x + u.re)) x := by
    have := (((hasDerivAt_id x).add_const u.re).pow 2).add_const (u.im ^ 2)
    simpa using this
  have h2 := (h1.log hne).div_const 2
  have e : (fun x : ℝ => Real.log ‖(x : ℂ) + u‖) =
      fun x => Real.log ((x + u.re) ^ 2 + u.im ^ 2) / 2 := funext fun x => logNorm_eq u x
  rw [e]
  refine h2.congr_deriv ?_
  unfold ln1
  field_simp

theorem hasDerivAt_ln1 (u : ℂ) {x : ℝ} (hv : 0 < x + u.re) :
    HasDerivAt (ln1 u) (ln2 u x) x := by
  have hne : (x + u.re) ^ 2 + u.im ^ 2 ≠ 0 := by positivity
  have hn : HasDerivAt (fun x : ℝ => x + u.re) 1 x := by simpa using (hasDerivAt_id x).add_const u.re
  have hd : HasDerivAt (fun x : ℝ => (x + u.re) ^ 2 + u.im ^ 2) (2 * (x + u.re)) x := by
    have := (hn.pow 2).add_const (u.im ^ 2)
    simpa using this
  have h := hn.div hd hne
  refine h.congr_deriv ?_
  unfold ln2
  field_simp
  ring

theorem ln2_le {u : ℂ} {x vmin : ℝ} (hv : 0 < vmin) (h : vmin ≤ x + u.re) :
    ln2 u x ≤ 1 / (8 * vmin ^ 2) := by
  have hx : 0 < x + u.re := lt_of_lt_of_le hv h
  have hd : 0 < (x + u.re) ^ 2 + u.im ^ 2 := by positivity
  have h1 : ln2 u x ≤ 1 / (8 * (x + u.re) ^ 2) := by
    unfold ln2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (u.im ^ 2 - 3 * (x + u.re) ^ 2)]
  refine h1.trans ?_
  apply one_div_le_one_div_of_le (by positivity)
  have := pow_le_pow_left₀ hv.le h 2
  linarith

/-- **LD16, the atom bound (integrated).**  Let `σ` be a finite measure carried by `Re u ≥ vmin > 0`.
For `a(x) = ω(x) + 2 ∫ log |x + u| dσ` (`= ω(x) - 2U^σ(-x)`) on `[0, K']` with a quadratic majorant
of `ω` of curvature `M₁`, one has `a(x) ≤ a(x*) + A (x - x*) - (M₁ - 2 c σ(ℂ)) (x - x*)²/2` with
`c = 1/(8 vmin²)` and `A = ω'(x*) + 2 ∫ Re (x* + u)⁻¹ dσ`. -/
theorem atom_quad_bound {σ : Measure ℂ} [IsFiniteMeasure σ] {vmin K' xs M₁ : ℝ} (hv : 0 < vmin)
    (hK' : 0 < K') (hxs : xs ∈ Ioo 0 K')
    (hsupp : ∀ᵐ u ∂σ, vmin ≤ u.re)
    (hint : ∀ x ∈ Icc 0 K', Integrable (fun u => Real.log ‖(x : ℂ) + u‖) σ)
    (hint1 : Integrable (fun u => ln1 u xs) σ)
    {ω : ℝ → ℝ} {ω' : ℝ}
    (hω : ∀ x ∈ Icc 0 K', ω x ≤ ω xs + ω' * (x - xs) - M₁ / 2 * (x - xs) ^ 2) :
    ∀ x ∈ Icc 0 K',
      ω x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤
        (ω xs + 2 * ∫ u, Real.log ‖(xs : ℂ) + u‖ ∂σ) +
        (ω' + 2 * ∫ u, ln1 u xs ∂σ) * (x - xs) -
        (M₁ - 2 * (1 / (8 * vmin ^ 2)) * σ.real univ) / 2 * (x - xs) ^ 2 := by
  intro x hx
  set c : ℝ := 1 / (8 * vmin ^ 2) with hc
  have hpt : ∀ᵐ u ∂σ, Real.log ‖(x : ℂ) + u‖ ≤
      Real.log ‖(xs : ℂ) + u‖ + ln1 u xs * (x - xs) + c / 2 * (x - xs) ^ 2 := by
    filter_upwards [hsupp] with u hu
    have hvx : ∀ y ∈ Icc (0 : ℝ) K', 0 < y + u.re := fun y hy => by
      have := hy.1; linarith
    have hcont : ContinuousOn (fun y : ℝ => Real.log ‖(y : ℂ) + u‖) (Icc 0 K') := by
      intro y hy
      have := (hasDerivAt_logNorm u (hvx y hy)).continuousAt
      exact this.continuousWithinAt
    have := quad_majorant_Icc (f := fun y : ℝ => Real.log ‖(y : ℂ) + u‖) (f' := ln1 u)
      (f'' := ln2 u) (a := 0) (b := K') (M := -c) hK'
      (fun y hy => hasDerivAt_logNorm u (hvx y (Ioo_subset_Icc_self hy)))
      (fun y hy => hasDerivAt_ln1 u (hvx y (Ioo_subset_Icc_self hy)))
      (fun y hy => by
        have := ln2_le (u := u) (x := y) hv (by linarith [hy.1])
        simpa [hc] using this) hxs hcont x hx
    simpa [sub_eq_add_neg, neg_div] using this
  have hA : Integrable (fun u : ℂ => Real.log ‖(xs : ℂ) + u‖) σ :=
    hint xs (Ioo_subset_Icc_self hxs)
  have hB : Integrable (fun u : ℂ => ln1 u xs * (x - xs)) σ := hint1.mul_const _
  have hC : Integrable (fun _ : ℂ => c / 2 * (x - xs) ^ 2) σ := integrable_const _
  have hAB : Integrable (fun u : ℂ => Real.log ‖(xs : ℂ) + u‖ + ln1 u xs * (x - xs)) σ :=
    hA.add hB
  have hrhs : Integrable (fun u : ℂ => Real.log ‖(xs : ℂ) + u‖ + ln1 u xs * (x - xs)
      + c / 2 * (x - xs) ^ 2) σ := hAB.add hC
  have hmono := integral_mono_ae (hint x hx) hrhs hpt
  have hval : ∫ u, (Real.log ‖(xs : ℂ) + u‖ + ln1 u xs * (x - xs) + c / 2 * (x - xs) ^ 2) ∂σ =
      (∫ u, Real.log ‖(xs : ℂ) + u‖ ∂σ) + (∫ u, ln1 u xs ∂σ) * (x - xs)
        + σ.real univ * (c / 2 * (x - xs) ^ 2) := by
    rw [integral_add hAB hC, integral_add hA hB, integral_mul_const, integral_const, smul_eq_mul]
  rw [hval] at hmono
  have h1 := hω x hx
  have hm0 : 0 ≤ σ.real univ := measureReal_nonneg
  nlinarith

/-- The binomial weight exponent `ω(x) = r [K log K - x log x - (K-x) log (K-x)]
+ e [(B+x) log (B+x) - x log x - B log B]`. -/
def omegaF (e r B K x : ℝ) : ℝ :=
  r * (K * Real.log K - x * Real.log x - (K - x) * Real.log (K - x))
    + e * ((B + x) * Real.log (B + x) - x * Real.log x - B * Real.log B)

def omegaD1 (e r B K x : ℝ) : ℝ :=
  -r * Real.log x + r * Real.log (K - x) + e * Real.log (B + x) - e * Real.log x

def omegaD2 (e r B K x : ℝ) : ℝ := -r / x - r / (K - x) + e / (B + x) - e / x

theorem hasDerivAt_omegaF (e r B K : ℝ) {x : ℝ} (h0 : 0 < x) (hK : x < K) (hB : 0 < B) :
    HasDerivAt (omegaF e r B K) (omegaD1 e r B K x) x := by
  have hx : x ≠ 0 := h0.ne'
  have hKx : K - x ≠ 0 := by linarith
  have hBx : B + x ≠ 0 := by linarith
  have a1 := Real.hasDerivAt_mul_log hx
  have a2 := (Real.hasDerivAt_mul_log hKx).comp x ((hasDerivAt_id x).const_sub K)
  have a3 := (Real.hasDerivAt_mul_log hBx).comp x ((hasDerivAt_id x).const_add B)
  have t1 := (((hasDerivAt_const x (K * Real.log K)).sub a1).sub a2).const_mul r
  have t2 := ((a3.sub a1).sub_const (B * Real.log B)).const_mul e
  refine (t1.add t2).congr_deriv ?_
  unfold omegaD1
  simp
  ring

theorem hasDerivAt_omegaD1 (e r B K : ℝ) {x : ℝ} (h0 : 0 < x) (hK : x < K) (hB : 0 < B) :
    HasDerivAt (omegaD1 e r B K) (omegaD2 e r B K x) x := by
  have hx : x ≠ 0 := h0.ne'
  have hKx : K - x ≠ 0 := by linarith
  have hBx : B + x ≠ 0 := by linarith
  have a1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  have a2 := (Real.hasDerivAt_log hKx).comp x ((hasDerivAt_id x).const_sub K)
  have a3 := (Real.hasDerivAt_log hBx).comp x ((hasDerivAt_id x).const_add B)
  have t := ((((a1.const_mul (-r)).add (a2.const_mul r)).add (a3.const_mul e)).sub
    (a1.const_mul e))
  refine t.congr_deriv ?_
  unfold omegaD2
  simp
  field_simp
  ring

theorem continuous_omegaF (e r B K : ℝ) : Continuous (omegaF e r B K) := by
  have h1 := Real.continuous_mul_log
  have h2 : Continuous fun x : ℝ => (K - x) * Real.log (K - x) :=
    h1.comp (continuous_const.sub continuous_id)
  have h3 : Continuous fun x : ℝ => (B + x) * Real.log (B + x) :=
    h1.comp (continuous_const.add continuous_id)
  unfold omegaF
  fun_prop

/-- The quadratic majorant of `ω` from `ω'' ≤ -M₁` on `(0, K)`. -/
theorem omega_majorant (e r B K : ℝ) {M₁ xs : ℝ} (hB : 0 < B) (hxs : xs ∈ Ioo 0 K)
    (hM : ∀ x ∈ Ioo 0 K, omegaD2 e r B K x ≤ -M₁) :
    ∀ x ∈ Icc 0 K, omegaF e r B K x ≤
      omegaF e r B K xs + omegaD1 e r B K xs * (x - xs) - M₁ / 2 * (x - xs) ^ 2 :=
  quad_majorant_Icc (hxs.1.trans hxs.2) (fun x hx => hasDerivAt_omegaF e r B K hx.1 hx.2 hB)
    (fun x hx => hasDerivAt_omegaD1 e r B K hx.1 hx.2 hB) hM hxs
    (continuous_omegaF e r B K).continuousOn

/-- **LD16 (assembled).**  With the quadratic majorant of `ω` and a positive effective curvature
`m = M₁ - 2 σ(ℂ)/(8 vmin²)`, the atom function is bounded on `[0, K']` by its value at `x*` plus
`A²/(2m)`, where `A = ω'(x*) + 2 ∫ Re (x* + u)⁻¹ dσ`. -/
theorem atom_sup_le {σ : Measure ℂ} [IsFiniteMeasure σ] {vmin K' xs M₁ : ℝ} (hv : 0 < vmin)
    (hK' : 0 < K') (hxs : xs ∈ Ioo 0 K')
    (hsupp : ∀ᵐ u ∂σ, vmin ≤ u.re)
    (hint : ∀ x ∈ Icc 0 K', Integrable (fun u => Real.log ‖(x : ℂ) + u‖) σ)
    (hint1 : Integrable (fun u => ln1 u xs) σ)
    {ω : ℝ → ℝ} {ω' : ℝ}
    (hω : ∀ x ∈ Icc 0 K', ω x ≤ ω xs + ω' * (x - xs) - M₁ / 2 * (x - xs) ^ 2)
    (hm : 0 < M₁ - 2 * (1 / (8 * vmin ^ 2)) * σ.real univ) :
    ∀ x ∈ Icc 0 K',
      ω x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤
        (ω xs + 2 * ∫ u, Real.log ‖(xs : ℂ) + u‖ ∂σ) +
        (ω' + 2 * ∫ u, ln1 u xs ∂σ) ^ 2 /
          (2 * (M₁ - 2 * (1 / (8 * vmin ^ 2)) * σ.real univ)) :=
  quad_sup_le hm (atom_quad_bound hv hK' hxs hsupp hint hint1 hω)

/-! ### W4: the cross-energy cell integral (LD14) -/

theorem integral_abs_pow5 {r : ℝ} (hr : 0 ≤ r) :
    ∫ u in (-r)..r, |u| ^ 5 = r ^ 6 / 3 := by
  have h1 : ∫ u in (-r)..0, |u| ^ 5 = r ^ 6 / 6 := by
    have : ∫ u in (-r)..0, |u| ^ 5 = ∫ u in (-r)..0, (-u) ^ 5 := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [uIcc_of_le (by linarith)] at hu
      simp only [abs_of_nonpos hu.2]
    rw [this]
    have hd : ∀ u ∈ uIcc (-r) 0, HasDerivAt (fun u : ℝ => -(u ^ 6 / 6)) ((-u) ^ 5) u := by
      intro u _
      have := ((hasDerivAt_pow 6 u).div_const 6).neg
      refine this.congr_deriv ?_
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  have h2 : ∫ u in (0 : ℝ)..r, |u| ^ 5 = r ^ 6 / 6 := by
    have : ∫ u in (0 : ℝ)..r, |u| ^ 5 = ∫ u in (0 : ℝ)..r, u ^ 5 := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [uIcc_of_le hr] at hu
      simp only [abs_of_nonneg hu.1]
    rw [this, integral_pow]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    h1, h2]
  ring

/-- **LD14 (cell integral).**  If `f` has an order-5 tower on `[c - r, c + r]` and
`|f 5| / 5! ≤ E` there, then `∫ f 0 ≤ 2 (b₀ r + b₂ r³/3 + b₄ r⁵/5) + E r⁶/3`, `b_j = f j c / j!`. -/
theorem cell_integral_le {f : ℕ → ℝ → ℝ} {c r E : ℝ} (hr : 0 ≤ r) (hf : IsTower f c r 5)
    (hE : ∀ x ∈ Icc (c - r) (c + r), |f 5 x| / 120 ≤ E) :
    ∫ x in (c - r)..(c + r), f 0 x ≤
      2 * (f 0 c * r + f 2 c / 2 * (r ^ 3 / 3) + f 4 c / 24 * (r ^ 5 / 5)) + E * (r ^ 6 / 3) := by
  have hE0 : 0 ≤ E := by
    have hc : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
    exact (div_nonneg (abs_nonneg _) (by norm_num)).trans (hE c hc)
  have hbd : ∀ x ∈ Icc (c - r) (c + r), |f 5 x| ≤ 120 * E := fun x hx => by
    have := hE x hx
    rw [div_le_iff₀ (by norm_num)] at this
    linarith
  have htay := taylor_tower' c r (120 * E) 5 f hf.cont (fun j hj x hx => hf.der j hj x hx) hbd
  -- pointwise bound
  set T : ℝ → ℝ := fun u => f 0 c + f 1 c * u + f 2 c / 2 * u ^ 2 + f 3 c / 6 * u ^ 3
    + f 4 c / 24 * u ^ 4 with hT
  have hpt : ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ T (x - c) + E * |x - c| ^ 5 := by
    intro x hx
    have h := htay x hx
    have h5 : (120 : ℝ) * E * |x - c| ^ 5 / ((5 : ℕ)! : ℝ) = E * |x - c| ^ 5 := by
      norm_num [Nat.factorial]; ring
    rw [h5] at h
    have hs : ∑ j ∈ Finset.range 5, f j c * (x - c) ^ j / (j ! : ℝ) = T (x - c) := by
      simp [Finset.sum_range_succ, hT, Nat.factorial]
      ring
    rw [hs] at h
    linarith [(abs_le.mp h).2]
  have hint0 : IntervalIntegrable (f 0) MeasureTheory.volume (c - r) (c + r) :=
    (hf.cont 0 (by norm_num)).intervalIntegrable_of_Icc (by linarith)
  have hcT : Continuous fun x : ℝ => T (x - c) + E * |x - c| ^ 5 := by
    simp only [hT]; fun_prop
  have hmono := intervalIntegral.integral_mono_on (by linarith : c - r ≤ c + r) hint0
    (hcT.intervalIntegrable _ _) hpt
  refine hmono.trans (le_of_eq ?_)
  -- evaluate
  have hsplit : ∫ x in (c - r)..(c + r), (T (x - c) + E * |x - c| ^ 5) =
      (∫ x in (c - r)..(c + r), T (x - c)) + E * ∫ x in (c - r)..(c + r), |x - c| ^ 5 := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; simp only [hT]; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]
  rw [hsplit]
  have e1 : ∫ x in (c - r)..(c + r), T (x - c) = ∫ u in (-r)..r, T u := by
    have := intervalIntegral.integral_comp_sub_right (a := c - r) (b := c + r) T c
    rw [this]; congr 1 <;> ring
  have e2 : ∫ x in (c - r)..(c + r), |x - c| ^ 5 = ∫ u in (-r)..r, |u| ^ 5 := by
    have := intervalIntegral.integral_comp_sub_right (a := c - r) (b := c + r)
      (fun u : ℝ => |u| ^ 5) c
    rw [this]; congr 1 <;> ring
  rw [e1, e2, integral_abs_pow5 hr]
  have hd : ∀ u ∈ uIcc (-r) r, HasDerivAt (fun u : ℝ => f 0 c * u + f 1 c * (u ^ 2 / 2)
      + f 2 c / 2 * (u ^ 3 / 3) + f 3 c / 6 * (u ^ 4 / 4) + f 4 c / 24 * (u ^ 5 / 5)) (T u) u := by
    intro u _
    have a1 := (hasDerivAt_id u).const_mul (f 0 c)
    have a2 := ((hasDerivAt_pow 2 u).div_const 2).const_mul (f 1 c)
    have a3 := ((hasDerivAt_pow 3 u).div_const 3).const_mul (f 2 c / 2)
    have a4 := ((hasDerivAt_pow 4 u).div_const 4).const_mul (f 3 c / 6)
    have a5 := ((hasDerivAt_pow 5 u).div_const 5).const_mul (f 4 c / 24)
    refine ((((a1.add a2).add a3).add a4).add a5).congr_deriv ?_
    simp only [hT]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; simp only [hT]; fun_prop)]
  ring

/-- **LD14 (partition).**  An exact partition `a 0 < ⋯ < a n` of the interval, with the cell
integral bound of `cell_integral_le` for each cell, bounds `∫_{a 0}^{a n} f` by the sum. -/
theorem partition_integral_le {f : ℝ → ℝ} {a : ℕ → ℝ} {Bd : ℕ → ℝ} (n : ℕ)
    (hint : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (a i) (a (i + 1)))
    (hB : ∀ i < n, ∫ x in (a i)..(a (i + 1)), f x ≤ Bd i) :
    ∫ x in (a 0)..(a n), f x ≤ ∑ i ∈ Finset.range n, Bd i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  exact Finset.sum_le_sum fun i hi => hB i (Finset.mem_range.mp hi)

end

end CatalanCore.Decay.WedgeBounds
