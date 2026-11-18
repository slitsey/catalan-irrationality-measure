module
public import CatalanCore.Li2.DecayCert.Compile.DiscCoeff
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem segCoeff_value (d : QSegment) (hh : cqReal d.half ≠ 0) (φ e : CQ)
    (hφ : 1 < ‖cqReal φ‖) (R : ℝ) (hR : 0 < R)
    (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive (d.toSegment hh) (jJ (cqReal φ))
      (cqReal e/cqReal d.half) R G)
    (y b : ℕ → ℂ)
    (hy : HasTaylorSeriesAt (fun u => (jq (jJ (cqReal φ)+(cqReal e/cqReal d.half)*u))⁻¹) y 0)
    (hb : HasTaylorSeriesAt G b 0) (n : ℕ) :
    cqReal (segCoeff d φ e (n+1))=b (n+1) := by
  let ζ := cqScale (1/2) (cqAdd φ (cqInv φ))
  let q := cqScale (1/2) (cqSub φ (cqInv φ))
  let γ := cqDiv e d.half
  have hζ : cqReal ζ=jJ (cqReal φ) := by
    dsimp only [ζ]
    rw [cqReal_scale,cqReal_add,cqReal_inv]
    unfold jJ
    push_cast
    ring
  have hγ : cqReal γ=cqReal e/cqReal d.half := cqReal_div e d.half
  have hs : 1 < jc (cqReal ζ) := by rw [hζ]; exact one_lt_jc_jJ hφ
  have hq : cqReal q=jq (cqReal ζ) := by
    dsimp only [q]
    rw [cqReal_scale,cqReal_sub,cqReal_inv,hζ]
    unfold jq
    rw [jphi_jJ hφ]
    push_cast
    ring
  have hy' : HasTaylorSeriesAt (fun u => (jq (cqReal ζ+cqReal γ*u))⁻¹) y 0 := by
    simpa only [hζ,hγ] using hy
  let f : ℕ → ℂ := fun j => cqReal (qShiftCoeff d.density ζ γ j)
  let r : ℕ → ℂ := fun j => cqReal (qShiftCoeff d.quotDensity ζ γ j)
  have hf : HasTaylorSeriesAt (fun u => (fpoly (d.toSegment hh).c (d.toSegment hh).N).eval (cqReal ζ+cqReal γ*u)) f 0 := by
    have ht := polynomial_affine_hasTaylorSeriesAt_zero (d.density.map (Rat.castHom ℂ)) (cqReal ζ) (cqReal γ)
    simpa only [f,qShiftCoeff_spec,qDensity_complex d hh] using ht
  have hr : HasTaylorSeriesAt (fun u => (rpoly (d.toSegment hh).c (d.toSegment hh).N).eval (cqReal ζ+cqReal γ*u)) r 0 := by
    have ht := polynomial_affine_hasTaylorSeriesAt_zero (d.quotDensity.map (Rat.castHom ℂ)) (cqReal ζ) (cqReal γ)
    simpa only [r,qShiftCoeff_spec,qQuotDensity_complex d hh] using ht
  have hG' : IsDiscSegmentPrimitive (d.toSegment hh) (cqReal ζ) (cqReal γ) R G := by
    simpa only [hζ,hγ] using hG
  have he := discPrimitive_coeff_recurrence (d.toSegment hh) (cqReal ζ) (cqReal γ) R hR G hG' f r y b hf hr hy' hb n
  have hyv (j : ℕ) : cqReal (yPair ζ γ q j).2=y j := (yPair_value ζ γ q hs hq y hy' j).2
  simp only [segCoeff,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right]
  change cqReal (cqScale (1/((n+1:ℕ):ℚ)) (cqMul γ (cqSub
    (cqSum ((List.range (n+1)).map (fun i : ℕ => cqMul (qShiftCoeff d.density ζ γ i) (yPair ζ γ q (n-i)).2)))
    (qShiftCoeff d.quotDensity ζ γ n))))=b (n+1)
  rw [cqReal_scale,cqReal_mul,cqReal_sub,cqReal_cqSum,List.map_map,list_sum_map_range]
  simp only [Function.comp_apply,cqReal_mul,hyv]
  have hn : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  dsimp only [f,r] at he
  push_cast
  field_simp [hn]
  push_cast at he
  linear_combination -he

theorem segConstant_value (terms : ℕ) (d : QSegment) (φ : CQ) (hφ : cqReal φ ≠ 0) :
    (segConstant terms d φ).value = (d.c 0:ℝ)*Real.log ‖cqReal d.half‖+
      ((d.c 0:ℂ)*Complex.log (cqReal φ/2)-
        ∑ k ∈ Finset.range (d.coeff.length-1),
          (d.c (k+1):ℂ)*(cqReal φ)⁻¹^(k+1)/(k+1:ℕ)).re := by
  have hn : Real.log ‖cqReal φ/2‖=Real.log ‖cqReal φ‖-Real.log 2 := by
    rw [norm_div,Complex.norm_two,Real.log_div (norm_ne_zero_iff.mpr hφ) (by norm_num)]
  have hc (k : ℕ) : ((cqPow (cqInv φ) (k+1)).1:ℝ)=((cqReal φ)⁻¹^(k+1)).re := by
    rw [← cqReal_re,cqReal_pow,cqReal_inv]
  have hrc (q : ℚ) : (q:ℂ).re=(q:ℝ) := by rw [← Complex.ofReal_ratCast,Complex.ofReal_re]
  have hic (q : ℚ) : (q:ℂ).im=0 := by rw [← Complex.ofReal_ratCast,Complex.ofReal_im]
  unfold segConstant
  rw [seSub_value,seScale_value,seSub_value,seAdd_value,seLogNorm_value,seLogNorm_value,seRat_value,
    list_sum_map_range]
  simp only [ScalarExpr.value]
  norm_num only [Rat.cast_ofNat]
  simp only [Complex.sub_re,Complex.mul_re,Complex.re_sum,Complex.div_natCast_re,
    Complex.log_re,hrc,hic,zero_mul,sub_zero,hn]
  push_cast
  simp only [hc]
  ring

#print axioms segConstant_value

#print axioms segCoeff_value
end
end CatalanCore.Li2.DecayCert
