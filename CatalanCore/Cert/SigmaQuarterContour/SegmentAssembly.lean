module
public import CatalanCore.Cert.QuarterContour.SegmentFinite
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts0
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts1
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts2
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts3
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts4
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts5
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts6
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts7
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts8
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts9
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts10
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts11
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts12
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts13
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts14
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts15
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts16
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts17
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts18
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts19
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts20
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts21
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts22
public import CatalanCore.Cert.SigmaQuarterContour.SegmentFacts23
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour.SegmentAssembly
open CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
/-- Append soundness over abstract lists; never simplify membership in closed cell data. -/
private theorem append_all {α : Type} {P : α → Prop} {xs ys : List α}
    (hx : ∀ z∈xs,P z) (hy : ∀ z∈ys,P z) : ∀ z∈xs++ys,P z := by
  intro z hz
  rcases List.mem_append.mp hz with hz|hz
  · exact hx z hz
  · exact hy z hz
theorem sound (epsilon : ℚ) (b : QBox) (hb : b ∈ QuarterContour.SegmentFinite.cells)
    (x : ℝ) (hx1 : (b.1.1 : ℝ)/2^40 ≤ x) (hx2 : x ≤ (b.1.2.1 : ℝ)/2^40) :
    (((b.2.2.2.1 : ℚ)/2^32 : ℚ) : ℝ) ≤ QuarterContour.gQuarter epsilon pts x 0 := by
  let P : QBox → Prop := fun c => ∀ y : ℝ,(c.1.1 : ℝ)/2^40≤y → y≤(c.1.2.1 : ℝ)/2^40 →
    (((c.2.2.2.1 : ℚ)/2^32 : ℚ) : ℝ)≤QuarterContour.gQuarter epsilon pts y 0
  have hAll : ∀ c∈QuarterContour.SegmentFinite.cells,P c := by
    unfold QuarterContour.SegmentFinite.cells
    exact (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (append_all (SegmentFacts0.sound epsilon) (SegmentFacts1.sound epsilon)) (SegmentFacts2.sound epsilon)) (SegmentFacts3.sound epsilon)) (SegmentFacts4.sound epsilon)) (SegmentFacts5.sound epsilon)) (SegmentFacts6.sound epsilon)) (SegmentFacts7.sound epsilon)) (SegmentFacts8.sound epsilon)) (SegmentFacts9.sound epsilon)) (SegmentFacts10.sound epsilon)) (SegmentFacts11.sound epsilon)) (SegmentFacts12.sound epsilon)) (SegmentFacts13.sound epsilon)) (SegmentFacts14.sound epsilon)) (SegmentFacts15.sound epsilon)) (SegmentFacts16.sound epsilon)) (SegmentFacts17.sound epsilon)) (SegmentFacts18.sound epsilon)) (SegmentFacts19.sound epsilon)) (SegmentFacts20.sound epsilon)) (SegmentFacts21.sound epsilon)) (SegmentFacts22.sound epsilon)) (SegmentFacts23.sound epsilon))
  exact hAll b hb x hx1 hx2
end CatalanCore.Cert.SigmaQuarterContour.SegmentAssembly
#print axioms CatalanCore.Cert.SigmaQuarterContour.SegmentAssembly.sound
