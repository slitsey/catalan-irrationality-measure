module
public import CatalanCore.Cert.QuarterContour.ModelSumNode
public import CatalanCore.Cert.QuarterContour.ModelRay
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelSum
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.ModelFactors
open CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.SigmaQuarter

/-- A checked polynomial cell proves the original objective uniformly on the quarter-ray tube. -/
theorem ray_node_sound (epsilon mp : ℚ) (hepsilon : epsilon ≤ 1/1000)
    (m : Model.Params) (ps : List Pt) (js : List Jet) (cs : List ℤ) (b : QBox)
    (hm : Model.validParams m = true) (hdy : 0 < m.DY)
    (hdir : 5*m.DY = -12*m.DX)
    (horigin : 3000*m.X0+1250*m.Y0 = -321*(m.U : ℤ))
    (hi : Model.inputsOK inputScale m ps js = true) (hc : allCoeffs factors js = cs)
    (hn : ModelCellNode.nodeOK epsilon mp m cs denominator (Model.baseSum m ps)
      (Model.errorSum inputScale js) b = true)
    (hprob : ∑ k, QuarterContour.masses ps k = 1) (u delta : ℝ)
    (hdelta : |delta| ≤ (1/2^30 : ℝ))
    (hx1 : (b.1.1 : ℝ)/2^40 ≤ -107/1000-u+delta)
    (hx2 : -107/1000-u+delta ≤ (b.1.2.1 : ℝ)/2^40)
    (hy1 : (b.1.2.2.1 : ℝ)/2^40 ≤ (12/5)*u)
    (hy2 : (12/5)*u ≤ (b.1.2.2.2 : ℝ)/2^40) :
    (mp : ℝ) ≤ QuarterContour.gQuarter epsilon ps (-107/1000-u+delta) ((12/5)*u) := by
  apply model_node_sound epsilon mp hepsilon m ps js cs b hm hdy hi hc hn hprob
    (-107/1000-u+delta) ((12/5)*u) hx1 hx2 hy1 hy2
  rw [ray_tube_distance m (validParams_facts m hm).1 hdy hdir horigin u delta]
  exact hdelta
end CatalanCore.Cert.QuarterContour.ModelSum
#print axioms CatalanCore.Cert.QuarterContour.ModelSum.ray_node_sound