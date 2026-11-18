module
public import CatalanCore.Li2.DecayCert.FieldIntegral.Geometry
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Complex Polynomial Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

theorem qBeta_value (d : QSegment) (a : ℚ) : cqReal (cqAdd d.mid (a,0))=cqReal d.mid+(a:ℂ) := by
  rw [cqReal_add]
  norm_num [cqReal]

theorem qEta_value (d : QSegment) (a : ℚ) :
    cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half))= -(cqReal d.mid+(a:ℂ))/cqReal d.half := by
  rw [cqReal_neg,cqReal_div,qBeta_value,neg_div]

theorem vint_integral_left (d : QSegment) (a : ℚ) (w : VSeed)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hh : cqReal d.half ≠ 0) (hb : cqAdd d.mid (a,0)=d.half) :
    (vintExpr d a w).value=(∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.measure) := by
  have hβ : (d.segmentData hh).M+((a:ℝ):ℂ)=(d.segmentData hh).h := by
    have he := congrArg cqReal hb
    rw [qBeta_value] at he
    simpa only [QSegment.segmentData,Complex.ofReal_ratCast] using he
  have hv := Vint_closed (d.segmentData hh) hpos (a:ℝ) (.leftEnd hβ)
  have hr := weighted_tail_range d hh (a:ℝ)
    (fun j c => (-1:ℂ)^(j+1)*c/(j+1:ℕ)) (by intro j; simp)
  simp only [VintFormula] at hv
  rw [hr] at hv
  rw [vintExpr_value_left d hh a w hb]
  simpa only [QSegment.segmentData,SegmentData.ν,QSegment.measure,Complex.ofReal_ratCast] using hv.symm

theorem vint_integral_right (d : QSegment) (a : ℚ) (w : VSeed)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hh : cqReal d.half ≠ 0) (hb : cqAdd d.mid (a,0)=cqNeg d.half)
    (hn : cqAdd d.mid (a,0) ≠ d.half) :
    (vintExpr d a w).value=(∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.measure) := by
  have hβ : (d.segmentData hh).M+((a:ℝ):ℂ)= -(d.segmentData hh).h := by
    have he := congrArg cqReal hb
    rw [qBeta_value,cqReal_neg] at he
    simpa only [QSegment.segmentData,Complex.ofReal_ratCast] using he
  have hv := Vint_closed (d.segmentData hh) hpos (a:ℝ) (.rightEnd hβ)
  have hr := weighted_tail_range d hh (a:ℝ) (fun j c => c/(j+1:ℕ)) (by intro j; simp)
  simp only [VintFormula] at hv
  rw [hr] at hv
  rw [vintExpr_value_right d hh a w hb hn]
  simpa only [QSegment.segmentData,SegmentData.ν,QSegment.measure,Complex.ofReal_ratCast] using hv.symm

theorem vint_integral_generic (d : QSegment) (a : ℚ) (w : VSeed)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hg : vintGeometryCheck d a w=true)
    (hnl : cqAdd d.mid (a,0) ≠ d.half) (hnr : cqAdd d.mid (a,0) ≠ cqNeg d.half)
    (hreal : ¬ (d.mid.2=0 ∧ d.half.2=0)) :
    (vintExpr d a w).value=(∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.measure) := by
  have hh := vintGeometry_half_ne d a w hg
  let η := cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half))
  rcases vintGeometry_generic_line d a w hg hnl hnr hreal with ⟨hoff,hline⟩
  have hη : η= -((d.segmentData hh).M+((a:ℝ):ℂ))/(d.segmentData hh).h := by
    simpa only [QSegment.segmentData,Complex.ofReal_ratCast] using qEta_value d a
  have hl : ∀ᵐ (x : ℝ) ∂ωarc,
      Complex.log ((d.segmentData hh).M+((a:ℝ):ℂ)+(d.segmentData hh).h*(x:ℂ)) =
        Complex.log (-(d.segmentData hh).h)+Complex.log (η-(x:ℂ))+2*Real.pi*Complex.I*(w.branch:ℂ) := by
    filter_upwards [omegaArc_ae_Icc] with x hx
    simpa only [QSegment.segmentData,Complex.ofReal_ratCast] using hline x hx
  have hv := Vint_closed (d.segmentData hh) hpos (a:ℝ) (.generic η w.branch hη hoff hl)
  have hr := weighted_tail_range d hh (a:ℝ)
    (fun j c => c*(jphi η)⁻¹^(j+1)/(j+1:ℕ)) (by intro j; simp)
  simp only [VintFormula] at hv
  rw [hr] at hv
  rw [vintExpr_value_generic d hh a w hnl hnr hreal hoff]
  simpa only [QSegment.segmentData,SegmentData.ν,QSegment.measure,Complex.ofReal_ratCast] using hv.symm

theorem VintFormula_real_off_value (d : SegmentData) (a : ℝ)
    (hM : d.M.im=0) (hh : d.h.im=0)
    (hs : 1 < |(-(d.M+(a:ℂ))/d.h).re|) (hoff : 1 < jc (-(d.M+(a:ℂ))/d.h)) :
    VintFormula d a (.realLine hM hh hs.le) =
      (weightedCheb d a 0*Complex.log (jphi (-(d.M+(a:ℂ))/d.h)/2) -
        (∑ j ∈ Finset.range (d.N+1),
          weightedCheb d a (j+1)*(jphi (-(d.M+(a:ℂ))/d.h))⁻¹^(j+1)/(j+1:ℕ)) -
        weightedCheb d a 0).re +(weightedCheb d a 0).re*Real.log ‖d.h‖ := by
  let η : ℂ := -(d.M+(a:ℂ))/d.h
  have hb : |η.re| ≠ 1 := ne_of_gt hs
  have hw : (weightedCheb d a 0).im=0 := by
    simp [weightedCheb,Complex.mul_im,hM,hh]
  have hn : Real.log ‖jphi η/2‖=Real.log ‖jphi η‖-Real.log 2 := by
    rw [norm_div,Complex.norm_two,Real.log_div (norm_ne_zero_iff.mpr (jphi_ne_zero hoff)) (by norm_num)]
  change (weightedCheb d a 0).re*(Real.log ‖d.h‖-Real.log 2+
      (if |η.re|=1 then 0 else Real.log ‖jphi η‖)) -
      (∑ j ∈ Finset.range (d.N+1), (weightedCheb d a (j+1)*
        (if |η.re|=1 then η else (jphi η)⁻¹)^(j+1)).re/(j+1:ℕ)) -
      (weightedCheb d a 0).re =
    (weightedCheb d a 0*Complex.log (jphi η/2) -
      (∑ j ∈ Finset.range (d.N+1), weightedCheb d a (j+1)*(jphi η)⁻¹^(j+1)/(j+1:ℕ)) -
      weightedCheb d a 0).re +(weightedCheb d a 0).re*Real.log ‖d.h‖
  simp only [if_neg hb,Complex.sub_re,Complex.mul_re,Complex.re_sum,
    Complex.div_natCast_re,Complex.log_re,hw,zero_mul,sub_zero,hn]
  ring

theorem vint_integral_real (d : QSegment) (a : ℚ) (w : VSeed)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hg : vintGeometryCheck d a w=true)
    (hnl : cqAdd d.mid (a,0) ≠ d.half) (hnr : cqAdd d.mid (a,0) ≠ cqNeg d.half)
    (hreal : d.mid.2=0 ∧ d.half.2=0) :
    (vintExpr d a w).value=(∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.measure) := by
  have hh := vintGeometry_half_ne d a w hg
  let η := cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half))
  have hd := vintGeometry_real_off d a w hg hnl hnr hreal
  have hη : η= -((d.segmentData hh).M+((a:ℝ):ℂ))/(d.segmentData hh).h := by
    simpa only [QSegment.segmentData,Complex.ofReal_ratCast] using qEta_value d a
  have hM : (d.segmentData hh).M.im=0 := by simp [QSegment.segmentData,cqReal,hreal.1]
  have hhalf : (d.segmentData hh).h.im=0 := by simp [QSegment.segmentData,cqReal,hreal.2]
  have hstrict : 1 < |(-((d.segmentData hh).M+((a:ℝ):ℂ))/(d.segmentData hh).h).re| := by
    rw [← hη]
    exact hd.2
  have hoff : 1 < jc (-((d.segmentData hh).M+((a:ℝ):ℂ))/(d.segmentData hh).h) := by
    rw [← hη]
    exact hd.1
  have hv := Vint_closed (d.segmentData hh) hpos (a:ℝ) (.realLine hM hhalf hstrict.le)
  rw [VintFormula_real_off_value _ _ hM hhalf hstrict hoff,← hη] at hv
  have hr := weighted_tail_range d hh (a:ℝ)
    (fun j c => c*(jphi η)⁻¹^(j+1)/(j+1:ℕ)) (by intro j; simp)
  rw [hr] at hv
  rw [vintExpr_value_real d hh a w hnl hnr hreal hd.1]
  simpa only [QSegment.segmentData,SegmentData.ν,QSegment.measure,Complex.ofReal_ratCast] using hv.symm

theorem vintExpr_eq_integral (d : QSegment) (a : ℚ) (w : VSeed)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hg : vintGeometryCheck d a w=true) :
    (vintExpr d a w).value=(∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.measure) := by
  by_cases hl : cqAdd d.mid (a,0)=d.half
  · exact vint_integral_left d a w hpos (vintGeometry_half_ne d a w hg) hl
  by_cases hr : cqAdd d.mid (a,0)=cqNeg d.half
  · exact vint_integral_right d a w hpos (vintGeometry_half_ne d a w hg) hr hl
  by_cases hre : d.mid.2=0 ∧ d.half.2=0
  · exact vint_integral_real d a w hpos hg hl hr hre
  · exact vint_integral_generic d a w hpos hg hl hr hre

theorem vintExpr_sound (d : QSegment) (a : ℚ) (w : VSeed)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,
      0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hg : vintGeometryCheck d a w=true) (b : QBox) (hc : (vintExpr d a w).check=some b) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.measure) ∈ Icc (b.1:ℝ) (b.2:ℝ) := by
  rw [← vintExpr_eq_integral d a w hpos hg]
  exact scalarCheck_sound _ b hc

#print axioms VintFormula_real_off_value
#print axioms vint_integral_real
#print axioms vintExpr_eq_integral
#print axioms vintExpr_sound

#print axioms qBeta_value
#print axioms qEta_value
#print axioms vint_integral_left
#print axioms vint_integral_right
#print axioms vint_integral_generic
end
end CatalanCore.Li2.DecayCert
