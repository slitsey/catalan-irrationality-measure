module
public import CatalanCore.Li2.DecayCert.Bent.Defs
public import CatalanCore.Li2.DecayCert.Covers
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section
theorem integral_log_horizontal_all (z : ℂ) (B : ℝ) (hB : 0 ≤ B) :
    (∫ x in (0:ℝ)..B,Real.log ‖z+(x:ℂ)‖)=freValue (z+(B:ℂ))-freValue z := by
  by_cases him : z.im=0
  · have hz : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
    rw [hz]
    have he : (fun x : ℝ => Real.log ‖(z.re:ℂ)+(x:ℂ)‖)=(fun x => Real.log (z.re+x)) := by
      funext x
      rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
    rw [he,intervalIntegral.integral_comp_add_left,integral_log]
    simp only [freValue,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.log_re,zero_mul,sub_zero,Complex.add_re,Complex.add_im,add_zero,
      ← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
    ring
  · have hslit (x : ℝ) (hx : x ∈ uIcc (0:ℝ) B) : z+(x:ℂ) ∈ Complex.slitPlane := by
      right
      simpa using him
    have hderiv (x : ℝ) (hx : x ∈ uIcc (0:ℝ) B) :
        HasDerivAt (fun x : ℝ => freValue (z+(x:ℂ))) (Real.log ‖z+(x:ℂ)‖) x := by
      let w : ℂ := z+(x:ℂ)
      have hs : w ∈ Complex.slitPlane := hslit x hx
      have hd : HasDerivAt (fun w : ℂ => w*Complex.log w-w) (Complex.log w) w := by
        have hf : (fun t : ℂ => t*Complex.log t-t)=id*Complex.log-id := by funext t; rfl
        rw [hf]
        convert ((hasDerivAt_id w).mul (Complex.hasDerivAt_log hs)).sub (hasDerivAt_id w) using 1
        simp only [id_eq]
        field_simp [Complex.slitPlane_ne_zero hs] <;> ring
      have ha : HasDerivAt (fun y : ℂ => z+y) 1 (x:ℂ) := (hasDerivAt_id' (x:ℂ)).const_add z
      have hh := (hd.comp (x:ℂ) ha).real_of_complex
      simpa only [freValue,Function.comp_apply,mul_one,Complex.log_re] using hh
    have hcont : ContinuousOn (fun x : ℝ => Real.log ‖z+(x:ℂ)‖) (uIcc (0:ℝ) B) := by
      apply ContinuousOn.log (by fun_prop)
      intro x hx
      exact norm_ne_zero_iff.mpr (Complex.slitPlane_ne_zero (hslit x hx))
    have hv := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    simpa only [Complex.ofReal_zero,add_zero] using hv

theorem phi0_primitive (z : ℂ) :
    phi0 z=3*freValue (z+1)-2*freValue z-freValue (z+4) := by
  change 3*(∫ x in (0:ℝ)..1,Real.log ‖z+(x:ℂ)‖)-
    (∫ x in (0:ℝ)..4,Real.log ‖z+(x:ℂ)‖)=_
  rw [integral_log_horizontal_all z 1 (by norm_num),integral_log_horizontal_all z 4 (by norm_num)]
  norm_num only [Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

theorem datum_re_integrable (d : DualDatum) : Integrable (fun u : ℂ => u.re) d.σ := by
  haveI := d.finite
  apply (integrable_const d.radius).mono' (by fun_prop)
  filter_upwards [d.bounded] with u hu
  exact (Complex.abs_re_le_norm u).trans hu

theorem datum_im_integrable (d : DualDatum) : Integrable (fun u : ℂ => u.im) d.σ := by
  haveI := d.finite
  apply (integrable_const d.radius).mono' (by fun_prop)
  filter_upwards [d.bounded] with u hu
  exact (Complex.abs_im_le_norm u).trans hu

theorem datum_fre_integrable (d : DualDatum) (a : ℝ) :
    Integrable (fun u => freValue (u+(a:ℂ))) d.σ := by
  haveI := d.finite
  have hl : Integrable (fun u : ℂ => Real.log ‖u+(a:ℂ)‖) d.σ := by
    have h := d.pointLogIntegrable (-(a:ℂ))
    have he (u : ℂ) : ‖-(a:ℂ)-u‖=‖u+(a:ℂ)‖ := by
      rw [show -(a:ℂ)-u= -(u+(a:ℂ)) by ring,norm_neg]
    simpa only [he] using h
  have h1 : Integrable (fun u : ℂ => (u+(a:ℂ)).re*Real.log ‖u+(a:ℂ)‖) d.σ := by
    apply hl.bdd_mul (by fun_prop)
    filter_upwards [d.bounded] with u hu
    change |u.re+a| ≤ d.radius+|a|
    exact (abs_add_le _ _).trans (add_le_add (Complex.abs_re_le_norm u |>.trans hu) (le_refl _))
  have h2 : Integrable (fun u : ℂ => (u+(a:ℂ)).im*Complex.arg (u+(a:ℂ))) d.σ := by
    simp only [Complex.add_im,Complex.ofReal_im,add_zero]
    apply (datum_im_integrable d).mul_bdd ((Complex.measurable_arg.comp (show Measurable (fun u : ℂ => u+(a:ℂ)) by fun_prop)).aestronglyMeasurable)
    exact ae_of_all _ (fun u => by change |Complex.arg (u+(a:ℂ))| ≤ Real.pi; exact Complex.abs_arg_le_pi (u+(a:ℂ)))
  have h3 := (datum_re_integrable d).add (integrable_const a)
  convert (h1.sub h2).sub h3 using 1
  funext u
  simp [freValue,Complex.mul_re,Complex.log_re,Complex.log_im]

theorem datum_V_integrable (z : ℝ) (d : DualDatum) : Integrable (V z) d.σ := by
  have hphi : Integrable phi0 d.σ := by
    have h1 := (datum_fre_integrable d 1).const_mul 3
    have h0 := (datum_fre_integrable d 0).const_mul 2
    have h4 := datum_fre_integrable d 4
    convert (h1.sub h0).sub h4 using 1
    funext u
    simp only [Complex.ofReal_one,Complex.ofReal_zero,Complex.ofReal_ofNat,add_zero,phi0_primitive,Pi.sub_apply]
  exact (hphi.add ((datum_re_integrable d).const_mul (Real.log |z|))).sub
    (((datum_im_integrable d).norm).const_mul (kappaRate z))

theorem datum_U_integrable (d : DualDatum) : Integrable (U d.σ) d.σ := by
  have he : U d.σ=CatalanCore.Li2.Uniform.pot d.σ := by
    funext u
    change -(∫ y,Real.log ‖u-y‖ ∂d.σ)=(∫ y,-Real.log ‖u-y‖ ∂d.σ)
    rw [integral_neg]
  rw [he]
  exact CatalanCore.Li2.Uniform.datum_energy_integrable d

#print axioms phi0_primitive
#print axioms datum_fre_integrable
#print axioms datum_V_integrable
#print axioms datum_U_integrable
end
end CatalanCore.Li2.DecayCert
