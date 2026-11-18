module
public import CatalanCore.Li2.DecayCert.Source.Sound
public import CatalanCore.Li2.Decay.Atoms
public import Mathlib.Analysis.Complex.RealDeriv
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

noncomputable def freValue (z : ℂ) : ℝ := (z*Complex.log z-z).re

theorem integral_log_horizontal (z : ℂ) (hz : 0 ≤ z.re) (B : ℝ) (hB : 0 ≤ B) :
    (∫ x in (0:ℝ)..B,Real.log ‖z+(x:ℂ)‖)=freValue (z+(B:ℂ))-freValue z := by
  by_cases hzero : z=0
  · subst z
    simp only [zero_add]
    simp_rw [Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
    rw [integral_log]
    simp [freValue,Complex.mul_re,Complex.log_re,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
  · have hslit (x : ℝ) (hx : x ∈ uIcc (0:ℝ) B) : z+(x:ℂ) ∈ Complex.slitPlane := by
      have hx0 : 0 ≤ x := by simpa only [min_eq_left hB] using hx.1
      by_cases him : z.im=0
      · have hr : 0 < z.re := by
          apply lt_of_le_of_ne hz
          intro hre
          apply hzero
          apply Complex.ext <;> simp [← hre,him]
        left
        simp only [Complex.add_re,Complex.ofReal_re]
        linarith
      · right
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

theorem phi0_eq_freValue (z : ℂ) (hz : 0 ≤ z.re) :
    phi0 z=3*freValue (z+1)-2*freValue z-freValue (z+4) := by
  change 3*(∫ x in (0:ℝ)..1,Real.log ‖z+(x:ℂ)‖)-
    (∫ x in (0:ℝ)..4,Real.log ‖z+(x:ℂ)‖)=_
  rw [integral_log_horizontal z hz 1 (by norm_num),integral_log_horizontal z hz 4 (by norm_num)]
  norm_num only [Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

#print axioms integral_log_horizontal
#print axioms phi0_eq_freValue
end
end CatalanCore.Li2.DecayCert
