module
public import CatalanCore.Cert.QuarterContour.ModelSumGeometry
public import CatalanCore.Cert.QuarterContour.ModelCell
public import CatalanCore.Cert.QuarterContour.ModelCellNode
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelSum
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.ModelFactors
open CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.SigmaQuarter

/-- A verified cell evaluator is a lower bound for the full smoothed potential. -/
theorem sigma_node_lower (epsilon mp : ℚ) (m : Model.Params) (ps : List Pt)
    (js : List Jet) (cs : List ℤ) (b : QBox)
    (hm : Model.validParams m = true) (hdy : 0 < m.DY)
    (hi : Model.inputsOK inputScale m ps js = true) (hc : allCoeffs factors js = cs)
    (hn : ModelCellNode.nodeOK epsilon mp m cs denominator (Model.baseSum m ps)
      (Model.errorSum inputScale js) b = true)
    (hprob : ∑ k, QuarterContour.masses ps k = 1) (x y : ℝ)
    (hy : (b.1.2.2.1 : ℝ)/2^40 ≤ y ∧ y ≤ (b.1.2.2.2 : ℝ)/2^40)
    (hd : ‖(⟨x,y⟩ : ℂ)-modelZ m (((m.U : ℝ)*y-m.Y0)/m.DY)‖ ≤ (1/2^30 : ℝ)) :
    (QuarterCompute.ModelCell.sigmaLower m cs denominator (Model.baseSum m ps)
      (Model.errorSum inputScale js) b.1.2.2.1 b.1.2.2.2 : ℝ)/
        (QuarterCompute.ModelCell.H : ℝ) ≤ SigmaP6.Usig ps x y := by
  have hU := (validParams_facts m hm).1
  have hvi := ModelCell.vInterval_contains m hU hdy b.1.2.2.1 b.1.2.2.2 y hy
  have hv := ModelCellNode.abs_le_one_of_nodeOK epsilon mp m cs denominator
    (Model.baseSum m ps) (Model.errorSum inputScale js) b hn _ hvi
  have ha := sigma_model_tube m (((m.U : ℝ)*y-m.Y0)/m.DY) ps js cs (⟨x,y⟩ : ℂ)
    hm hi hv hc hd hprob
  exact ModelCell.lower_sound m cs denominator (Model.baseSum m ps)
    (Model.errorSum inputScale js) b.1.2.2.1 b.1.2.2.2 y (SigmaP6.Usig ps x y)
    hU hdy (by decide) hy ha

/-- A checked cell now proves the original quarter-ray objective from exact model data. -/
theorem model_node_sound (epsilon mp : ℚ) (hepsilon : epsilon ≤ 1/1000)
    (m : Model.Params) (ps : List Pt) (js : List Jet) (cs : List ℤ) (b : QBox)
    (hm : Model.validParams m = true) (hdy : 0 < m.DY)
    (hi : Model.inputsOK inputScale m ps js = true) (hc : allCoeffs factors js = cs)
    (hn : ModelCellNode.nodeOK epsilon mp m cs denominator (Model.baseSum m ps)
      (Model.errorSum inputScale js) b = true)
    (hprob : ∑ k, QuarterContour.masses ps k = 1) (x y : ℝ)
    (hx1 : (b.1.1 : ℝ)/2^40 ≤ x) (hx2 : x ≤ (b.1.2.1 : ℝ)/2^40)
    (hy1 : (b.1.2.2.1 : ℝ)/2^40 ≤ y) (hy2 : y ≤ (b.1.2.2.2 : ℝ)/2^40)
    (hd : ‖(⟨x,y⟩ : ℂ)-modelZ m (((m.U : ℝ)*y-m.Y0)/m.DY)‖ ≤ (1/2^30 : ℝ)) :
    (mp : ℝ) ≤ QuarterContour.gQuarter epsilon ps x y := by
  apply ModelCellNode.node_sound epsilon mp hepsilon m ps cs denominator
    (Model.baseSum m ps) (Model.errorSum inputScale js) b hn x y hx1 hx2 hy1 hy2
  exact sigma_node_lower epsilon mp m ps js cs b hm hdy hi hc hn hprob x y ⟨hy1,hy2⟩ hd
end CatalanCore.Cert.QuarterContour.ModelSum
#print axioms CatalanCore.Cert.QuarterContour.ModelSum.model_node_sound