module
public import CatalanCore.Li2.DecayCert.Bent.Analytic
public import CatalanCore.Li2.DecayCert.Bent.Moments
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

theorem oneVExpr_value (z : ℚ) (hz : z < 0) (s : QSegment) (w : VSeed×VSeed×VSeed)
    (terms : ℕ) (d : DualDatum) (hμ : s.measure ≤ d.σ)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x)
    (him : ∀ᵐ u : ℂ ∂s.measure,0 ≤ u.im)
    (h1 : vintGeometryCheck s 1 w.1=true)
    (h0 : vintGeometryCheck s 0 w.2.1=true)
    (h4 : vintGeometryCheck s 4 w.2.2=true) :
    (oneVExpr z s w terms).value=∫ u,V (z:ℝ) u ∂s.measure := by
  have hf1 := (datum_fre_integrable d 1).mono_measure hμ
  have hf0 := (datum_fre_integrable d 0).mono_measure hμ
  have hf4 := (datum_fre_integrable d 4).mono_measure hμ
  have hr := (datum_re_integrable d).mono_measure hμ
  have hi := (datum_im_integrable d).mono_measure hμ
  have hiabs : Integrable (fun u : ℂ => |u.im|) s.measure := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hv1 : (vintExpr s 1 w.1).value=∫ u,freValue (u+1) ∂s.measure := by
    simpa only [freValue,Rat.cast_one] using vintExpr_eq_integral s 1 w.1 hpos h1
  have hv0 : (vintExpr s 0 w.2.1).value=∫ u,freValue u ∂s.measure := by
    simpa only [freValue,Rat.cast_zero,add_zero] using vintExpr_eq_integral s 0 w.2.1 hpos h0
  have hv4 : (vintExpr s 4 w.2.2).value=∫ u,freValue (u+4) ∂s.measure := by
    simpa only [freValue,Rat.cast_ofNat] using vintExpr_eq_integral s 4 w.2.2 hpos h4
  have hnorm : (∫ u : ℂ,|u.im| ∂s.measure)=∫ u : ℂ,u.im ∂s.measure :=
    integral_congr_ae (him.mono (fun u hu => abs_of_nonneg hu))
  have him0 : (0:ℝ) ≤ ((cqAdd (cqScale (s.c 0) s.mid) (cqScale (s.c 1/2) s.half)).2:ℝ) := by
    rw [← qsegment_im_moment s hpos]
    exact integral_nonneg_of_ae him
  have hfun : V (z:ℝ)=(fun u => 3*freValue (u+1)-2*freValue u-freValue (u+4)+
      Real.log |(z:ℝ)| *u.re-Real.pi*|u.im|) := by
    funext u
    rw [V,phi0_primitive,kappaRate,if_neg (show ¬(0:ℝ)<(z:ℝ) by exact_mod_cast not_lt.mpr hz.le)]
  rw [hfun]
  dsimp only
  simp only [Complex.ofReal_one,Complex.ofReal_zero,Complex.ofReal_ofNat,add_zero] at hf1 hf0 hf4
  have e1 := integral_sub ((((hf1.const_mul 3).sub (hf0.const_mul 2)).sub hf4).add
    (hr.const_mul (Real.log |(z:ℝ)|))) (hiabs.const_mul Real.pi)
  have e2 := integral_add (((hf1.const_mul 3).sub (hf0.const_mul 2)).sub hf4)
    (hr.const_mul (Real.log |(z:ℝ)|))
  have e3 := integral_sub ((hf1.const_mul 3).sub (hf0.const_mul 2)) hf4
  have e4 := integral_sub (hf1.const_mul 3) (hf0.const_mul 2)
  simp only [Pi.add_apply,Pi.sub_apply] at e1 e2 e3 e4
  rw [e1,e2,e3,e4]
  simp only [integral_const_mul,hnorm,qsegment_re_moment s hpos,qsegment_im_moment s hpos]
  simp only [oneVExpr,seSum,List.foldl_cons,List.foldl_nil,seAdd_value,seScale_value,
    seSub_value,seRat_value,seNeg,ScalarExpr.value,List.map_cons,List.map_nil,
    Rat.cast_zero,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_abs,abs_of_nonneg him0,hv1,hv0,hv4]
  ring
#print axioms oneVExpr_value
end
end CatalanCore.Li2.DecayCert
