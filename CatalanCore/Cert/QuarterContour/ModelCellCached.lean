module
public import CatalanCore.Cert.QuarterCompute.ModelCellCached
public import CatalanCore.Cert.QuarterContour.ModelCellNode
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelCellCached
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

/-- Numerically identical to ModelCellNode.nodeOK after one coefficient-list equality. -/
def nodeOK (epsilon mp : ℚ) (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (cints : List Interval) (base : ℤ) (error : ℕ) (b : QBox) : Bool :=
  decide (boxGeom b) &&
  decide (-H ≤ (vInterval p b.1.2.2.1 b.1.2.2.2).1 ∧
    (vInterval p b.1.2.2.1 b.1.2.2.2).2 ≤ H) &&
  decide (mp ≤ QuarterContour.quarterBoxLB epsilon
    ((QuarterCompute.ModelCellCached.sigmaLower p cints base error
      b.1.2.2.1 b.1.2.2.2 : ℤ)/(2^48 : ℚ))
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2)

theorem nodeOK_eq (epsilon mp : ℚ) (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (cints : List Interval) (base : ℤ) (error : ℕ) (b : QBox)
    (hc : cints = coefficients H (denom : ℤ) cs) :
    nodeOK epsilon mp p cints base error b =
      ModelCellNode.nodeOK epsilon mp p cs denom base error b := by
  unfold nodeOK ModelCellNode.nodeOK
  rw [QuarterCompute.ModelCellCached.sigmaLower_eq p cs denom cints base error _ _ hc]

theorem node_sound
    (epsilon mp : ℚ) (hepsilon : epsilon ≤ 1/1000)
    (p : CatalanCore.Cert.QuarterCompute.Model.Params) (pts : List Pt)
    (cs : List ℤ) (denom : ℕ) (cints : List Interval) (base : ℤ) (error : ℕ) (b : QBox)
    (hcoeffs : cints = coefficients H (denom : ℤ) cs)
    (hc : nodeOK epsilon mp p cints base error b = true)
    (x y : ℝ) (hx1 : (b.1.1 : ℝ)/2^40 ≤ x) (hx2 : x ≤ (b.1.2.1 : ℝ)/2^40)
    (hy1 : (b.1.2.2.1 : ℝ)/2^40 ≤ y) (hy2 : y ≤ (b.1.2.2.2 : ℝ)/2^40)
    (hS : (QuarterCompute.ModelCellCached.sigmaLower p cints base error
      b.1.2.2.1 b.1.2.2.2 : ℝ)/(H : ℝ) ≤ SigmaP6.Usig pts x y) :
    (mp : ℝ) ≤ QuarterContour.gQuarter epsilon pts x y := by
  rw [nodeOK_eq epsilon mp p cs denom cints base error b hcoeffs] at hc
  rw [QuarterCompute.ModelCellCached.sigmaLower_eq p cs denom cints base error _ _ hcoeffs] at hS
  exact ModelCellNode.node_sound epsilon mp hepsilon p pts cs denom base error b hc
    x y hx1 hx2 hy1 hy2 hS
end CatalanCore.Cert.QuarterContour.ModelCellCached
#print axioms CatalanCore.Cert.QuarterContour.ModelCellCached.nodeOK_eq
#print axioms CatalanCore.Cert.QuarterContour.ModelCellCached.node_sound
