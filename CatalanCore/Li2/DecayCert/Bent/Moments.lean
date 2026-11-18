module
public import CatalanCore.Li2.DecayCert.Bent.Defs
public import CatalanCore.Li2.DecayCert.Covers
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
noncomputable section

theorem qsegment_cos_moment (s : QSegment) :
    (∫ θ,chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)*Real.cos θ ∂arc)=(s.c 1:ℝ)/2 := by
  have h := integral_chebF_mul_T (fun k => (s.c k:ℝ)) (s.coeff.length-1) 1
  simp only [Int.ofNat_one,Chebyshev.T_one,Polynomial.eval_X,one_ne_zero,ite_false] at h
  by_cases hn : 1 ≤ s.coeff.length-1
  · simpa only [if_pos hn,div_eq_mul_inv,one_mul] using h
  · have hc : s.c 1=0 := by
      unfold QSegment.c
      rw [List.getElem?_eq_none (by omega)]
      rfl
    simpa only [if_neg hn,hc,Rat.cast_zero,zero_div] using h

theorem qsegment_linear_moment (s : QSegment)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x)
    (a b : ℝ) :
    (∫ θ,chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)*(a+b*Real.cos θ) ∂arc)=
      a*(s.c 0:ℝ)+b*(s.c 1:ℝ)/2 := by
  have hc : Integrable (fun θ => chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)*Real.cos θ) arc := by
    apply (integrable_chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1)).mul_bdd (by fun_prop)
    exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one θ)
  have he (θ : ℝ) : chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)*(a+b*Real.cos θ)=
      a*chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)+
      b*(chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ)*Real.cos θ) := by ring
  simp_rw [he]
  rw [integral_add ((integrable_chebF _ _).const_mul a) (hc.const_mul b),
    integral_const_mul,integral_const_mul,integral_chebF,qsegment_cos_moment]
  ring

theorem qsegment_re_moment (s : QSegment)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) :
    (∫ u : ℂ,u.re ∂s.measure)=((cqAdd (cqScale (s.c 0) s.mid) (cqScale (s.c 1/2) s.half)).1:ℝ) := by
  change (∫ u : ℂ,u.re ∂segMeasure _ _ _ _)=_
  rw [integral_segMeasure hpos (by fun_prop)]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [qsegment_linear_moment s hpos]
  simp only [cqReal,cqAdd,cqScale,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,sub_zero]
  push_cast
  simp only [← Complex.ofReal_ratCast,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem qsegment_im_moment (s : QSegment)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) :
    (∫ u : ℂ,u.im ∂s.measure)=((cqAdd (cqScale (s.c 0) s.mid) (cqScale (s.c 1/2) s.half)).2:ℝ) := by
  change (∫ u : ℂ,u.im ∂segMeasure _ _ _ _)=_
  rw [integral_segMeasure hpos (by fun_prop)]
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
  rw [qsegment_linear_moment s hpos]
  simp only [cqReal,cqAdd,cqScale,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,sub_zero]
  push_cast
  simp only [← Complex.ofReal_ratCast,Complex.ofReal_re,Complex.ofReal_im]
  ring
#print axioms qsegment_cos_moment
#print axioms qsegment_re_moment
#print axioms qsegment_im_moment
end
end CatalanCore.Li2.DecayCert
