module
public import CatalanCore.Cert.QuarterContour.CancelLog
public import CatalanCore.Cert.QuarterContour.NearSlice
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.CancelLogSlice
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def macroLB (near : List Pt) (m : Macro) (b : Quad) : ℚ :=
  SigmaP6.sigTL m.x0 m.y0 m.fd b.1 b.2.1 b.2.2.1 b.2.2.2
    (CancelLog.sigSum b.1 b.2.1 b.2.2.1 b.2.2.2 near)

lemma macroLB_eq (near : List Pt) (m : Macro) (b : Quad) :
    macroLB near m b = NearSlice.macroLB near m b := by
  simp only [macroLB,NearSlice.macroLB,CancelLog.sigSum_eq]

def rayOK (epsilon : ℚ) (near : List Pt) (mp : ℚ) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b =>
    decide (QuarterCompute.FastNode.boxGeom b) &&
    decide (mp ≤ QuarterCompute.FastNode.quarterBoxLB epsilon (macroLB near m b.1)
      b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2))

lemma rayOK_eq_slice (epsilon : ℚ) (near : List Pt) (mp : ℚ) (m : Macro) :
    rayOK epsilon near mp m = NearSlice.rayOK epsilon near mp m := by
  simp only [rayOK,NearSlice.rayOK,macroLB_eq]

lemma rayOK_eq (epsilon : ℚ) (pts near : List Pt) (mp : ℚ) (m : Macro)
    (hnear : macroNear pts m = near) :
    rayOK epsilon near mp m = QuarterContour.rayOK epsilon pts mp m :=
  (rayOK_eq_slice epsilon near mp m).trans (NearSlice.rayOK_eq epsilon pts near mp m hnear)
end CatalanCore.Cert.QuarterContour.CancelLogSlice
#print axioms CatalanCore.Cert.QuarterContour.CancelLogSlice.rayOK_eq
