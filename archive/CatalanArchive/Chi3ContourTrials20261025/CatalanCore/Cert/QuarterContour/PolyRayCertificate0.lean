module
public import CatalanCore.Cert.QuarterContour.PolyCertified0
public import CatalanCore.Cert.QuarterCompute.PolyCells0
public import CatalanCore.Cert.QuarterContour.ModelSumRay
public import CatalanCore.Cert.QuarterContour.ModelProbability
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PolyRayCertificate0
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.SigmaQuarter

/-- A member cell carries exactly the analytic model constants proved by its input ledger. -/
lemma checked_node (b : QBox) (hb : b ∈ PolyModel0.cells) :
    ModelCellNode.nodeOK (1/100000) (115867/50000) PolyModel0.params
      PolyModel0.coefficients ModelFactors.denominator
      (Model.baseSum PolyModel0.params pts)
      (Model.errorSum ModelFactors.inputScale PolyModel0.jets) b = true := by
  rw [PolyModel0.base_checked,PolyModel0.error_checked]
  exact (List.all_eq_true.mp PolyModel0.cells_checked) b hb

/-- The actual decoded model proves every member cell on the quarter-ray tube. -/
theorem ray_cell_sound (b : QBox) (hb : b ∈ PolyModel0.cells) (u delta : ℝ)
    (hdelta : |delta| ≤ (1/2^30 : ℝ))
    (hx1 : (b.1.1 : ℝ)/2^40 ≤ -107/1000-u+delta)
    (hx2 : -107/1000-u+delta ≤ (b.1.2.1 : ℝ)/2^40)
    (hy1 : (b.1.2.2.1 : ℝ)/2^40 ≤ (12/5)*u)
    (hy2 : (12/5)*u ≤ (b.1.2.2.2 : ℝ)/2^40) :
    ((115867/50000 : ℚ) : ℝ) ≤
      QuarterContour.gQuarter (1/100000) pts (-107/1000-u+delta) ((12/5)*u) := by
  exact ModelSum.ray_node_sound (1/100000) (115867/50000) (by norm_num)
    PolyModel0.params pts PolyModel0.jets PolyModel0.coefficients b
    PolyModel0.params_ok PolyModel0.dy_pos PolyModel0.ray_direction PolyModel0.ray_origin
    PolyModel0.inputs_ok PolyCertified0.coefficients_checked (checked_node b hb)
    probability_mass_sum u delta hdelta hx1 hx2 hy1 hy2
end CatalanCore.Cert.QuarterContour.PolyRayCertificate0
#print axioms CatalanCore.Cert.QuarterContour.PolyRayCertificate0.ray_cell_sound
