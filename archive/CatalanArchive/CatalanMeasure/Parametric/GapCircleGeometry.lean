module
public import CatalanArchive.CatalanMeasure.Parametric.GapNodal
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCircle
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Polynomial.Chebyshev
noncomputable section

theorem norm_square_sub_real_square (z : ℂ) (c : ℝ) :
    ‖z^2-(c:ℂ)^2‖^2=(‖z‖^2+c^2)^2-4*c^2*z.re^2 := by
  rw [Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,pow_two,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem gap_argument_complex_eval (a : ℝ) (z : ℂ) :
    ((gapArgument a).map (algebraMap ℝ ℂ)).eval z=
      (2*z^2-(1+(a:ℂ)^2))/(1-(a:ℂ)^2) := by
  simp only [gapArgument,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_pow,Polynomial.map_X,eval_sub,eval_mul,eval_C,eval_pow,eval_X,
    Complex.coe_algebraMap,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_add,
    Complex.ofReal_pow,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

theorem gap_argument_complex_distances {a : ℝ} (ha0 : 0<a) (ha1 : a<1) (z : ℂ) :
    ‖((gapArgument a).map (algebraMap ℝ ℂ)).eval z-1‖=
      2*‖z^2-1‖/(1-a^2) ∧
    ‖((gapArgument a).map (algebraMap ℝ ℂ)).eval z+1‖=
      2*‖z^2-(a:ℂ)^2‖/(1-a^2) := by
  have hd : 0<1-a^2 := by
    have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0<1+a)
    nlinarith only [hh]
  have hdc : (1:ℂ)-(a:ℂ)^2≠0 := by
    exact_mod_cast hd.ne'
  rw [gap_argument_complex_eval]
  constructor
  · have he : (2*z^2-(1+(a:ℂ)^2))/(1-(a:ℂ)^2)-1=
        2*(z^2-1)/(1-(a:ℂ)^2) := by field_simp; ring
    rw [he,norm_div,norm_mul,Complex.norm_ofNat]
    have hnorm : ‖(1:ℂ)-(a:ℂ)^2‖=1-a^2 := by
      rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    rw [hnorm]
  · have he : (2*z^2-(1+(a:ℂ)^2))/(1-(a:ℂ)^2)+1=
        2*(z^2-(a:ℂ)^2)/(1-(a:ℂ)^2) := by field_simp; ring
    rw [he,norm_div,norm_mul,Complex.norm_ofNat]
    have hnorm : ‖(1:ℂ)-(a:ℂ)^2‖=1-a^2 := by
      rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    rw [hnorm]

theorem gap_circle_radical_caps {a radius lo b1 b2 : ℝ}
    (hlo : 0≤lo) (ha : 0≤a) (hb1 : 0≤b1) (hb2 : 0≤b2)
    (hcap1 : (radius^2+1)^2-4*lo^2 ≤ b1^2)
    (hcap2 : (radius^2+a^2)^2-4*a^2*lo^2 ≤ b2^2)
    (z : ℂ) (hz : ‖z‖=radius) (hs : lo≤|z.re|) :
    ‖z^2-1‖≤b1 ∧ ‖z^2-(a:ℂ)^2‖≤b2 := by
  have hsq : lo^2≤z.re^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hlo hs 2
  have h1 := norm_square_sub_real_square z 1
  have h2 := norm_square_sub_real_square z a
  rw [hz] at h1 h2
  norm_num only [Complex.ofReal_one,one_pow,mul_one] at h1
  constructor
  · nlinarith only [h1,hcap1,hsq,norm_nonneg (z^2-1),hb1]
  · have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤4*a^2)
    nlinarith only [h2,hcap2,hh,norm_nonneg (z^2-(a:ℂ)^2),hb2]

theorem gap_circle_filter_sq {radius hi : ℝ} (z : ℂ) (hz : ‖z‖=radius)
    (hs : |z.re|≤hi) : ‖(1:ℂ)-z‖^2≤radius^2+1+2*hi := by
  have hnorm := Complex.sq_norm_sub_sq_re z
  rw [hz] at hnorm
  have he : ‖(1:ℂ)-z‖^2=(1-z.re)^2+z.im^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im]
    ring
  rw [he]
  have hh := (abs_le.mp hs).1
  nlinarith only [hnorm,hh]

end
end CatalanMeasure.Parametric
