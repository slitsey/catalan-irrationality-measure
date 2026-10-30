module
public import CatalanCore.Cert.QuarterCompute.Data
public import CatalanCore.Cert.SigmaQuarterContour.Data
public import CatalanCore.Cert.QuarterContour.Energy
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute

theorem pts_eq : pts = SigmaQuarterContour.pts := by rfl

theorem logLoS_eq (N : Nat) : logLoS N = CatalanLambda.Cert.logLoS N := by rfl

theorem iRow_eq (p : Pt) (qs : List Pt) : iRow p qs = QuarterContour.iRow p qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [iRow, QuarterContour.iRow, ih, logLoS_eq]
    rfl

theorem row_from_compute (r : Nat) (v : Int)
    (h : iRow (pointAt pts r) pts = v) :
    QuarterContour.iRow (QuarterContour.pointAt SigmaQuarterContour.pts r) SigmaQuarterContour.pts = v := by
  rw [iRow_eq, pts_eq] at h
  exact h
end CatalanCore.Cert.QuarterCompute
#print axioms CatalanCore.Cert.QuarterCompute.row_from_compute