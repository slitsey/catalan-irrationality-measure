module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section

/-!
# Green identity on a rectangle (iterated interval integrals, only `ContinuousOn` data)

`∬ (∂ₛG + ∂ₜH) = ∫ (G(b,·) - G(a,·)) + ∫ (H(·,d) - H(·,c))`
for `G, H` differentiable in one variable with derivatives continuous on the rectangle.
This is the divergence theorem used for the elementary boundary-energy identity.
-/

namespace CatalanCore.Uniform.Decay.Tools

open Set intervalIntegral

theorem green_rect (G H Dg Dh : ℝ → ℝ → ℝ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hDg : ContinuousOn (Function.uncurry Dg) (Icc a b ×ˢ Icc c d))
    (hDh : ContinuousOn (Function.uncurry Dh) (Icc a b ×ˢ Icc c d))
    (hG : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, HasDerivAt (fun x => G x t) (Dg s t) s)
    (hH : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, HasDerivAt (fun y => H s y) (Dh s t) t) :
    ∫ s in a..b, ∫ t in c..d, (Dg s t + Dh s t)
      = (∫ t in c..d, (G b t - G a t)) + ∫ s in a..b, (H s d - H s c) := by
  set c1 : ℝ → ℝ := fun x => max a (min b x) with hc1
  set c2 : ℝ → ℝ := fun x => max c (min d x) with hc2
  have hc1c : Continuous c1 := by fun_prop
  have hc2c : Continuous c2 := by fun_prop
  have hc1m : ∀ x, c1 x ∈ Icc a b := fun x =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hc2m : ∀ x, c2 x ∈ Icc c d := fun x =>
    ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩
  have hc1id : ∀ x ∈ Icc a b, c1 x = x := fun x hx => by
    simp only [hc1]; rw [min_eq_right hx.2, max_eq_right hx.1]
  have hc2id : ∀ x ∈ Icc c d, c2 x = x := fun x hx => by
    simp only [hc2]; rw [min_eq_right hx.2, max_eq_right hx.1]
  set Dg' : ℝ → ℝ → ℝ := fun s t => Dg (c1 s) (c2 t) with hDg'
  set Dh' : ℝ → ℝ → ℝ := fun s t => Dh (c1 s) (c2 t) with hDh'
  have hmaps : Continuous fun p : ℝ × ℝ => (c1 p.1, c2 p.2) := by fun_prop
  have hDg'c : Continuous (Function.uncurry Dg') :=
    hDg.comp_continuous hmaps (fun p => ⟨hc1m _, hc2m _⟩)
  have hDh'c : Continuous (Function.uncurry Dh') :=
    hDh.comp_continuous hmaps (fun p => ⟨hc1m _, hc2m _⟩)
  have hsec1 : ∀ s, Continuous fun t => Dg' s t := fun s =>
    hDg'c.comp (continuous_const.prodMk continuous_id)
  have hsec2 : ∀ s, Continuous fun t => Dh' s t := fun s =>
    hDh'c.comp (continuous_const.prodMk continuous_id)
  -- Step A: replace by clamped versions
  have hA : ∫ s in a..b, ∫ t in c..d, (Dg s t + Dh s t)
      = ∫ s in a..b, ∫ t in c..d, (Dg' s t + Dh' s t) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Icc a b := by simpa [uIcc_of_le hab] using hs
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc c d := by simpa [uIcc_of_le hcd] using ht
    simp only [hDg', hDh', hc1id s hs', hc2id t ht']
  -- Step B: split
  have hB : ∫ s in a..b, ∫ t in c..d, (Dg' s t + Dh' s t)
      = (∫ s in a..b, ∫ t in c..d, Dg' s t) + ∫ s in a..b, ∫ t in c..d, Dh' s t := by
    have : ∀ s, ∫ t in c..d, (Dg' s t + Dh' s t)
        = (∫ t in c..d, Dg' s t) + ∫ t in c..d, Dh' s t := fun s =>
      intervalIntegral.integral_add ((hsec1 s).intervalIntegrable _ _)
        ((hsec2 s).intervalIntegrable _ _)
    simp_rw [this]
    exact intervalIntegral.integral_add
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hDg'c c d).intervalIntegrable _ _)
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hDh'c c d).intervalIntegrable _ _)
  -- Step C: the t-derivative part
  have hC : ∫ s in a..b, ∫ t in c..d, Dh' s t = ∫ s in a..b, (H s d - H s c) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Icc a b := by simpa [uIcc_of_le hab] using hs
    have hcont : ContinuousOn (fun t => Dh s t) (Icc c d) :=
      hDh.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hs', ht⟩)
    have e : ∫ t in c..d, Dh' s t = ∫ t in c..d, Dh s t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Icc c d := by simpa [uIcc_of_le hcd] using ht
      simp only [hDh', hc1id s hs', hc2id t ht']
    rw [e]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hH s hs' t (by simpa [uIcc_of_le hcd] using ht))
      (hcont.intervalIntegrable_of_Icc hcd)
  -- Step D: the s-derivative part (swap)
  have hD : ∫ s in a..b, ∫ t in c..d, Dg' s t = ∫ t in c..d, (G b t - G a t) := by
    have hint : MeasureTheory.IntegrableOn (Function.uncurry Dg') (uIoc a b ×ˢ uIoc c d) := by
      have := hDg'c.continuousOn.integrableOn_compact (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))) (K := Icc a b ×ˢ Icc c d)
        (isCompact_Icc.prod isCompact_Icc)
      refine this.mono_set ?_
      rw [uIoc_of_le hab, uIoc_of_le hcd]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap hint]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc c d := by simpa [uIcc_of_le hcd] using ht
    have hcont : ContinuousOn (fun s => Dg s t) (Icc a b) :=
      hDg.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, ht'⟩)
    have e : ∫ s in a..b, Dg' s t = ∫ s in a..b, Dg s t := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' : s ∈ Icc a b := by simpa [uIcc_of_le hab] using hs
      simp only [hDg', hc1id s hs', hc2id t ht']
    rw [e]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hG s (by simpa [uIcc_of_le hab] using hs) t ht')
      (hcont.intervalIntegrable_of_Icc hab)
  rw [hA, hB, hC, hD, add_comm]

end CatalanCore.Uniform.Decay.Tools
