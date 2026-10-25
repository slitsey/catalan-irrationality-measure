module
public import CatalanCore.Cert.QuarterContour.AxisModelGeometry
public import CatalanCore.Cert.QuarterContour.FastAxisNodePure
public import CatalanCore.Cert.QuarterContour.ModelSumGeometry
public import CatalanCore.Cert.QuarterContour.Box
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.AxisModelNode
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.ModelFactors
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.QuarterContour.DyadicInterval
open CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterContour.AxisModelGeometry
open CatalanCore.Cert.SigmaQuarter

/-- Exact fixed-point evaluation on an axis interval has no tube error. -/
theorem lower_sound (m : Model.Params) (cs : List ℤ) (denom : ℕ)
    (cints : List Interval) (base : ℤ) (error : ℕ) (xl xh : ℤ) (x sigma : ℝ)
    (hU : 0 < m.U) (hDX : 0 < m.DX) (hden : 0 < denom)
    (hx : (xl : ℝ)/2^40 ≤ x ∧ x ≤ (xh : ℝ)/2^40)
    (hints : cints = coefficients H (denom : ℤ) cs)
    (ha : -(base : ℝ)/2^97+
      RealPolynomial.evalReal (((m.U : ℝ)*x-m.X0)/m.DX) cs/(denom : ℝ)-
      (error : ℝ)/2^64 ≤ sigma) :
    (AxisModelCell.sigmaLower m cints base error xl xh : ℝ)/(H : ℝ) ≤ sigma := by
  have hv := AxisModelGeometry.vInterval_contains m hU hDX xl xh x hx
  have hc := (coefficients_sound_normalized H (denom : ℤ) (by norm_num [H])
    (by exact_mod_cast hden) cs _ _ hv).1
  rw [← hints] at hc
  push_cast at hc
  have hb := ModelCell.base_floor base
  have he := ModelCell.error_ceil error
  apply le_trans _ ha
  unfold AxisModelCell.sigmaLower
  push_cast
  rw [sub_div,add_div]
  linarith only [hc,hb,he]

/-- The decoded model proves the exact axis sigma bound used by the pure checker. -/
theorem sigma_node_lower (m : Model.Params) (ps : List Pt) (js : List Jet)
    (cs : List ℤ) (cints : List Interval) (b : QBox)
    (hm : Model.validParams m = true) (hDX : 0 < m.DX)
    (hY : m.Y0 = 0) (hD : m.DY = 0)
    (hi : Model.inputsOK inputScale m ps js = true) (hc : allCoeffs factors js = cs)
    (hints : cints = coefficients H (denominator : ℤ) cs)
    (hrange : -H ≤ (AxisModelCell.vInterval m b.1.1 b.1.2.1).1 ∧
      (AxisModelCell.vInterval m b.1.1 b.1.2.1).2 ≤ H)
    (x : ℝ) (hx : (b.1.1 : ℝ)/2^40 ≤ x ∧ x ≤ (b.1.2.1 : ℝ)/2^40) :
    (AxisModelCell.sigmaLower m cints (Model.baseSum m ps)
      (Model.errorSum inputScale js) b.1.1 b.1.2.1 : ℝ)/(H : ℝ) ≤ SigmaP6.Usig ps x 0 := by
  have hU := (validParams_facts m hm).1
  have hvi := AxisModelGeometry.vInterval_contains m hU hDX b.1.1 b.1.2.1 x hx
  have hv := abs_le_one_of_range _ hrange _ hvi
  have ha := ModelSum.sigma_model_decoded m (((m.U : ℝ)*x-m.X0)/m.DX) ps js cs hm hi hv hc
  rw [axis_modelZ m hU hDX hY hD x] at ha
  exact lower_sound m cs denominator cints (Model.baseSum m ps)
    (Model.errorSum inputScale js) b.1.1 b.1.2.1 x (SigmaP6.Usig ps x 0)
    hU hDX (by decide) hx hints ha

/-- A pure per-cell check proves its own gamma on either real-axis branch. -/
theorem node_sound (epsilon : ℚ) (m : Model.Params) (ps : List Pt) (js : List Jet)
    (cs : List ℤ) (cints : List Interval) (b : QBox)
    (hm : Model.validParams m = true) (hDX : 0 < m.DX)
    (hY : m.Y0 = 0) (hD : m.DY = 0)
    (hi : Model.inputsOK inputScale m ps js = true) (hc : allCoeffs factors js = cs)
    (hints : cints = coefficients H (denominator : ℤ) cs)
    (hn : AxisModelCell.nodeOK m cints (Model.baseSum m ps)
      (Model.errorSum inputScale js) b = true)
    (x : ℝ) (hx1 : (b.1.1 : ℝ)/2^40 ≤ x) (hx2 : x ≤ (b.1.2.1 : ℝ)/2^40) :
    (((b.2.2.2.1 : ℚ)/2^32 : ℚ) : ℝ) ≤ QuarterContour.gQuarter epsilon ps x 0 := by
  simp only [AxisModelCell.nodeOK,Bool.and_eq_true,decide_eq_true_eq] at hn
  rcases hn with ⟨⟨hg,hrange⟩,hgamma⟩
  rw [FastAxisNodePure.axisGeom_eq] at hg
  simp only [FastAxisNodePure.quarterAxisLB_eq,FastAxisNodePure.axisUt_eq] at hgamma
  obtain ⟨hd1,hd2,hy1,hy2,hl,hh⟩ := hg
  have hlr : (b.2.1 : ℝ) ≤ 2*b.1.1/3 := by exact_mod_cast hl
  have hhr : 2*(b.1.2.1 : ℝ)/3 ≤ b.2.2.1 := by exact_mod_cast hh
  have hs := sigma_node_lower m ps js cs cints b hm hDX hY hD hi hc hints hrange x ⟨hx1,hx2⟩
  have hS : ((((AxisModelCell.sigmaLower m cints (Model.baseSum m ps)
      (Model.errorSum inputScale js) b.1.1 b.1.2.1 : ℤ)/(2^48 : ℚ)) : ℚ) : ℝ) ≤
      SigmaP6.Usig ps x 0 := by
    push_cast
    norm_num [H] at hs ⊢
    exact hs
  have ho := QuarterContour.quarterAxis_sound epsilon ps _
    (SigmaQuarter.axisUt b.1.1 b.1.2.1) (SigmaQuarter.axisUt b.2.1 b.2.2.1) x hS
    (SigmaQuarter.axisUt_sound _ _ hd1 x hx1 hx2)
    (SigmaQuarter.axisUt_sound _ _ hd2 (2*x/3) (by linarith) (by linarith))
  exact (Rat.cast_le.mpr hgamma).trans ho
end CatalanCore.Cert.QuarterContour.AxisModelNode
#print axioms CatalanCore.Cert.QuarterContour.AxisModelNode.node_sound
