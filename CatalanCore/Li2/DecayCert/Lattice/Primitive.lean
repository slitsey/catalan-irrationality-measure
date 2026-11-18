module
public import CatalanCore.Li2.DecayCert.Lattice.Primitive.Analytic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem integral_W_closed (z θ Y p q : ℝ) (hY : 0<Y)
    (hpq : 0≤p ∧ p≤q ∧ q≤Y) (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] [IsFiniteMeasure σ2]
    (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (R : ℝ)
    (hR : ∀ s∈Icc p q,|U σ2 (s:ℂ)-d.mpValue K s|≤R) :
    |(∫ s in p..q,W z (σ1+σ2) (s:ℂ)-θ)-
      (latticePrimitive z θ d K q-latticePrimitive z θ d K p)|≤2*R*(q-p) := by
  have hsub : Icc p q ⊆ Ici (0:ℝ) := fun s hs => hpq.1.trans hs.1
  have hmp : ContinuousOn (d.mpValue K) (Icc p q) :=
    (mp_real_continuousOn σ2 d.y0 d.y0_neg K).mono hsub
  have hUmeas : Measurable (fun s : ℝ => U σ2 (s:ℂ)) := by
    exact (CatalanCore.Lai.DecayEnergy.measurable_potC σ2).neg.comp Complex.continuous_ofReal.measurable
  let err : ℝ → ℝ := fun s => U σ2 (s:ℂ)-d.mpValue K s
  have hiErr : IntegrableOn err (Icc p q) := by
    apply (integrable_const R).mono'
      (hUmeas.aestronglyMeasurable.restrict.sub (hmp.aestronglyMeasurable measurableSet_Icc))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hR s hs
  have hiErrI : IntervalIntegrable err volume p q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpq.2.1).mpr hiErr
  have happrox : ContinuousOn (latticeApproxField z θ d K) (Icc p q) :=
    (latticeApproxField_continuousOn z θ d K).mono hsub
  have hiApprox : IntervalIntegrable (latticeApproxField z θ d K) volume p q :=
    happrox.intervalIntegrable_of_Icc hpq.2.1
  have hFTC : (∫ s in p..q,latticeApproxField z θ d K s)=
      latticePrimitive z θ d K q-latticePrimitive z θ d K p := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq.2.1
      ((latticePrimitive_continuousOn z θ d K).mono hsub) _ hiApprox
    intro s hs
    exact latticePrimitive_derivative z θ d K s (lt_of_le_of_lt hpq.1 hs.1)
  have hefield (s : ℝ) (hs : s∈Icc p q) :
      W z (σ1+σ2) (s:ℂ)-θ=latticeApproxField z θ d K s-2*err s := by
    have hs0 : 0≤s := hsub hs
    have ho := latticeOwn_source d hY s ⟨hs0,hs.2.trans hpq.2.2⟩
    have hi2 := latticeSecond_log_integrable d s hs0
    have hU : U (σ1+σ2) (s:ℂ)=U σ1 (s:ℂ)+U σ2 (s:ℂ) := by
      change -(∫ u,Real.log ‖(s:ℂ)-u‖ ∂(σ1+σ2))=
        -(∫ u,Real.log ‖(s:ℂ)-u‖ ∂σ1)+ -(∫ u,Real.log ‖(s:ℂ)-u‖ ∂σ2)
      rw [integral_add_measure ho.1 hi2]
      ring
    rw [W,hU,ho.2]
    dsimp only [latticeApproxField,err]
    ring
  have heI : (∫ s in p..q,W z (σ1+σ2) (s:ℂ)-θ)=
      (∫ s in p..q,latticeApproxField z θ d K s)-2*(∫ s in p..q,err s) := by
    calc
      _ = ∫ s in p..q,latticeApproxField z θ d K s-2*err s := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hefield s (by simpa only [uIcc_of_le hpq.2.1] using hs)
      _ = _ := by rw [intervalIntegral.integral_sub hiApprox (hiErrI.const_mul 2),intervalIntegral.integral_const_mul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a:=p) (b:=q) (f:=err) (C:=R) (by
    intro s hs
    have hsI : s∈Ioc p q := by simpa only [uIoc_of_le hpq.2.1] using hs
    have hs' : s∈Icc p q := ⟨hsI.1.le,hsI.2⟩
    exact hR s hs')
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hpq.2.1)] at hb
  rw [heI,hFTC]
  rw [show (latticePrimitive z θ d K q-latticePrimitive z θ d K p)-2*(∫ s in p..q,err s)-
    (latticePrimitive z θ d K q-latticePrimitive z θ d K p)= -2*(∫ s in p..q,err s) by ring]
  rw [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith
#print axioms integral_W_closed
end
end CatalanCore.Li2.DecayCert
