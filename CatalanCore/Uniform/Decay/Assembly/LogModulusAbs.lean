module

public import CatalanCore.Uniform.Decay.Assembly.LogModulus

@[expose] public section

/-!
# The log-modulus bound: abstract integral form (lane D, package D5a)

`integral_abs_log_diff_le`: for distance profiles `a, b` along `[0, L]` with
`|s - x| ≤ a s`, `|s - x'| ≤ b s`, `|a s - b s| ≤ δ`, `|x - x'| ≤ δ`, `0 < δ ≤ 1/4`:

  `∫_{(0,L]} |log a - log b| ≤ δ (17 + 14 |log δ| + 3 log (1 + L / (3 δ)))`.

No measurability hypothesis is needed (the majorant is integrable and the integrand is
nonnegative).
-/

namespace CatalanCore.Uniform.Decay.Assembly

open MeasureTheory Set intervalIntegral CatalanCore.Uniform.Decay.Tools

theorem integrableOn_bdd {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) {f : ℝ → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ s ∈ S, ‖f s‖ ≤ M) : IntegrableOn f S :=
  Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
    ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hb))

theorem integrable_indicator_inter {L : ℝ} {T : Set ℝ} (hT : MeasurableSet T) {φ : ℝ → ℝ}
    (h : IntegrableOn φ (Ioc 0 L ∩ T) volume) :
    Integrable (T.indicator φ) (volume.restrict (Ioc 0 L)) := by
  rw [integrable_indicator_iff hT, IntegrableOn, Measure.restrict_restrict hT, inter_comm]
  exact h

theorem volume_inter_ne_top (L : ℝ) (T : Set ℝ) : volume (Ioc 0 L ∩ T) ≠ ⊤ :=
  ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top).ne

/-- Main abstract integral bound. -/
theorem integral_abs_log_diff_le {a b : ℝ → ℝ} {x x' δ L : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hL : 0 ≤ L) (hxx' : |x - x'| ≤ δ)
    (ha : ∀ s ∈ Ioc 0 L, |s - x| ≤ a s) (hb : ∀ s ∈ Ioc 0 L, |s - x'| ≤ b s)
    (hab : ∀ s ∈ Ioc 0 L, |a s - b s| ≤ δ) :
    ∫ s in Ioc 0 L, |Real.log (a s) - Real.log (b s)|
      ≤ δ * (17 + 14 * |Real.log δ| + 3 * Real.log (1 + L / (3 * δ))) := by
  set α : ℝ := 3 * δ with hα
  have hα0 : 0 < α := by positivity
  set TR : Set ℝ := {s | x + α ≤ s} with hTR
  set TL : Set ℝ := {s | s ≤ x - α} with hTL
  set TN : Set ℝ := Ioo (x - α) (x + α) with hTN
  have mTR : MeasurableSet TR := measurableSet_Ici
  have mTL : MeasurableSet TL := measurableSet_Iic
  have mTN : MeasurableSet TN := measurableSet_Ioo
  set φR : ℝ → ℝ := fun s => (3 / 2) * δ * (s - x)⁻¹ with hφR
  set φL : ℝ → ℝ := fun s => (3 / 2) * δ * (x - s)⁻¹ with hφL
  set φN : ℝ → ℝ := fun s => 1 / 2 + |Real.log (s - x)| + |Real.log (s - x')| with hφN
  set h : ℝ → ℝ := fun s => TR.indicator φR s + TL.indicator φL s + TN.indicator φN s with hh
  -- integrabilities on the pieces
  have iR : IntegrableOn φR (Ioc 0 L ∩ TR) volume := by
    refine integrableOn_bdd (measurableSet_Ioc.inter mTR) (volume_inter_ne_top L TR)
      (by fun_prop) (M := 1 / 2) (fun s hs => ?_)
    have hs2 : x + α ≤ s := hs.2
    have h1 : 0 < s - x := by linarith
    rw [hφR]; simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv, div_le_iff₀ h1]
    nlinarith
  have iL : IntegrableOn φL (Ioc 0 L ∩ TL) volume := by
    refine integrableOn_bdd (measurableSet_Ioc.inter mTL) (volume_inter_ne_top L TL)
      (by fun_prop) (M := 1 / 2) (fun s hs => ?_)
    have hs2 : s ≤ x - α := hs.2
    have h1 : 0 < x - s := by linarith
    rw [hφL]; simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv, div_le_iff₀ h1]
    nlinarith
  have hsubN : Ioc 0 L ∩ TN ⊆ Ioc (x - α) (x + α) := fun s hs => ⟨hs.2.1, hs.2.2.le⟩
  have hsubN' : Ioc 0 L ∩ TN ⊆ Ioc (x' - 4 * δ) (x' + 4 * δ) := by
    intro s hs
    have h1 := hs.2.1; have h2 := hs.2.2
    have := abs_le.1 hxx'
    constructor <;> linarith [this.1, this.2]
  have hαle : α ≤ 1 := by linarith
  have h4le : 4 * δ ≤ 1 := by linarith
  have lN1 := setIntegral_abs_log_le x α hα0.le hαle hsubN
  have lN2 := setIntegral_abs_log_le x' (4 * δ) (by positivity) h4le hsubN'
  have iNc : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) (Ioc 0 L ∩ TN) volume :=
    integrableOn_const (volume_inter_ne_top L TN)
  have iN : IntegrableOn φN (Ioc 0 L ∩ TN) volume := (iNc.add lN1.1).add lN2.1
  have hI : Integrable h (volume.restrict (Ioc 0 L)) :=
    ((integrable_indicator_inter mTR iR).add (integrable_indicator_inter mTL iL)).add
      (integrable_indicator_inter mTN iN)
  -- pointwise majorisation
  have hmaj : ∀ s ∈ Ioc 0 L, s ≠ x → s ≠ x' →
      |Real.log (a s) - Real.log (b s)| ≤ h s := by
    intro s hs hsx hsx'
    have has := ha s hs; have hbs := hb s hs; have habs := hab s hs
    by_cases hR : x + α ≤ s
    · have hw : 3 * δ ≤ |s - x| := by rw [abs_of_pos (by linarith)]; linarith
      have := log_diff_far hδ0 hxx' has hbs habs hw
      have hnL : s ∉ TL := fun hh => by have : s ≤ x - α := hh; linarith
      have hnN : s ∉ TN := fun hh => by simp only [hTN, mem_Ioo] at hh; linarith [hh.2]
      simp only [hh, Set.indicator_of_mem (show s ∈ TR from hR), Set.indicator_of_notMem hnL,
        Set.indicator_of_notMem hnN, add_zero, hφR]
      rw [abs_of_pos (show 0 < s - x by linarith)] at this
      calc _ ≤ _ := this
        _ = _ := by rw [div_eq_mul_inv]
    · by_cases hLf : s ≤ x - α
      · have hw : 3 * δ ≤ |s - x| := by rw [abs_of_neg (by linarith)]; linarith
        have := log_diff_far hδ0 hxx' has hbs habs hw
        have hnR : s ∉ TR := hR
        have hnN : s ∉ TN := fun hh => by simp only [hTN, mem_Ioo] at hh; linarith [hh.1]
        simp only [hh, Set.indicator_of_notMem hnR, Set.indicator_of_mem (show s ∈ TL from hLf),
          Set.indicator_of_notMem hnN, zero_add, add_zero, hφL]
        rw [abs_of_neg (show s - x < 0 by linarith)] at this
        calc _ ≤ _ := this
          _ = _ := by rw [neg_sub, div_eq_mul_inv]
      · have hsN : s ∈ TN := ⟨by linarith, by linarith⟩
        have hnR : s ∉ TR := hR
        have hnL : s ∉ TL := hLf
        simp only [hh, Set.indicator_of_notMem hnR, Set.indicator_of_notMem hnL,
          Set.indicator_of_mem hsN, zero_add, hφN]
        exact log_diff_near hδ0 hδ hsx hsx' has hbs habs
  have hae : ∀ᵐ s ∂(volume.restrict (Ioc 0 L)),
      |Real.log (a s) - Real.log (b s)| ≤ h s := by
    have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ x := Measure.ae_ne _ _
    have h2 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ x' := Measure.ae_ne _ _
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2,
      ae_restrict_mem measurableSet_Ioc] with s h1 h2 h3
    exact hmaj s h3 h1 h2
  have step1 : ∫ s in Ioc 0 L, |Real.log (a s) - Real.log (b s)| ≤ ∫ s in Ioc 0 L, h s :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hI hae
  have jR : Integrable (fun s => TR.indicator φR s) (volume.restrict (Ioc 0 L)) :=
    integrable_indicator_inter mTR iR
  have jL : Integrable (fun s => TL.indicator φL s) (volume.restrict (Ioc 0 L)) :=
    integrable_indicator_inter mTL iL
  have jN : Integrable (fun s => TN.indicator φN s) (volume.restrict (Ioc 0 L)) :=
    integrable_indicator_inter mTN iN
  have jRL : Integrable (fun s => TR.indicator φR s + TL.indicator φL s)
      (volume.restrict (Ioc 0 L)) := jR.add jL
  have hsplit : ∫ s in Ioc 0 L, h s =
      (∫ s in Ioc 0 L ∩ TR, φR s) + (∫ s in Ioc 0 L ∩ TL, φL s) + ∫ s in Ioc 0 L ∩ TN, φN s := by
    rw [hh]; simp only
    rw [integral_add jRL jN, integral_add jR jL, setIntegral_indicator mTR,
      setIntegral_indicator mTL, setIntegral_indicator mTN]
  -- far integrals
  have fR := far_right x α L hα0 hL
  have fL := far_left x α L hα0 hL
  have eR : ∫ s in Ioc 0 L ∩ TR, φR s = (3 / 2) * δ * ∫ s in Ioc 0 L ∩ TR, (s - x)⁻¹ :=
    integral_const_mul _ _
  have eL : ∫ s in Ioc 0 L ∩ TL, φL s = (3 / 2) * δ * ∫ s in Ioc 0 L ∩ TL, (x - s)⁻¹ :=
    integral_const_mul _ _
  -- near integral
  have kN1 : Integrable (fun s => (1 / 2 : ℝ)) (volume.restrict (Ioc 0 L ∩ TN)) := iNc
  have kN2 : Integrable (fun s => |Real.log (s - x)|) (volume.restrict (Ioc 0 L ∩ TN)) := lN1.1
  have kN3 : Integrable (fun s => |Real.log (s - x')|) (volume.restrict (Ioc 0 L ∩ TN)) := lN2.1
  have kN12 : Integrable (fun s => (1 / 2 : ℝ) + |Real.log (s - x)|)
      (volume.restrict (Ioc 0 L ∩ TN)) := kN1.add kN2
  have eN : ∫ s in Ioc 0 L ∩ TN, φN s =
      (∫ s in Ioc 0 L ∩ TN, (1 / 2 : ℝ)) + (∫ s in Ioc 0 L ∩ TN, |Real.log (s - x)|)
        + ∫ s in Ioc 0 L ∩ TN, |Real.log (s - x')| := by
    rw [hφN]; simp only
    rw [integral_add kN12 kN3, integral_add kN1 kN2]
  have eC : ∫ s in Ioc 0 L ∩ TN, (1 / 2 : ℝ) ≤ α := by
    calc ∫ s in Ioc 0 L ∩ TN, (1 / 2 : ℝ) ≤ ∫ s in Ioc (x - α) (x + α), (1 / 2 : ℝ) :=
          setIntegral_mono_set (integrableOn_const (by simp)) (Filter.Eventually.of_forall
            (fun s => by norm_num)) (Filter.Eventually.of_forall hsubN)
      _ = α := by
          rw [← integral_of_le (by linarith : x - α ≤ x + α), intervalIntegral.integral_const]
          simp; ring
  -- logarithm comparisons
  have hlog : Real.log δ ≤ Real.log α := Real.log_le_log hδ0 (by linarith)
  have hlog4 : Real.log δ ≤ Real.log (4 * δ) := Real.log_le_log hδ0 (by linarith)
  have hl3 : Real.log α ≤ 0 := Real.log_nonpos hα0.le hαle
  have hl4 : Real.log (4 * δ) ≤ 0 := Real.log_nonpos (by positivity) h4le
  have habsd : |Real.log δ| = - Real.log δ := abs_of_nonpos (by linarith)
  have m1 : δ * Real.log δ ≤ δ * Real.log α := mul_le_mul_of_nonneg_left hlog hδ0.le
  have m2 : δ * Real.log δ ≤ δ * Real.log (4 * δ) := mul_le_mul_of_nonneg_left hlog4 hδ0.le
  have hLg : 0 ≤ Real.log (1 + L / α) :=
    Real.log_nonneg (by have : 0 ≤ L / α := div_nonneg hL hα0.le; linarith)
  have hfR : (3 / 2) * δ * ∫ s in Ioc 0 L ∩ TR, (s - x)⁻¹
      ≤ (3 / 2) * δ * Real.log (1 + L / α) :=
    mul_le_mul_of_nonneg_left fR (by positivity)
  have hfL : (3 / 2) * δ * ∫ s in Ioc 0 L ∩ TL, (x - s)⁻¹
      ≤ (3 / 2) * δ * Real.log (1 + L / α) :=
    mul_le_mul_of_nonneg_left fL (by positivity)
  have hLN1 := lN1.2
  have hLN2 := lN2.2
  rw [hsplit, eR, eL, eN] at step1
  have e3 : δ * (17 + 14 * |Real.log δ| + 3 * Real.log (1 + L / (3 * δ))) =
      17 * δ - 14 * (δ * Real.log δ) + 3 * δ * Real.log (1 + L / α) := by
    rw [habsd, hα]; ring
  rw [e3]
  have hαδ : α = 3 * δ := hα
  -- explicit expansions of the two log-moment bounds
  have x1 : 2 * (α - α * Real.log α) = 6 * δ - 6 * (δ * Real.log α) := by rw [hαδ]; ring
  have x2 : 2 * (4 * δ - 4 * δ * Real.log (4 * δ)) = 8 * δ - 8 * (δ * Real.log (4 * δ)) := by ring
  nlinarith [step1, hfR, hfL, eC, hLN1, hLN2, m1, m2, x1, x2]

end CatalanCore.Uniform.Decay.Assembly
