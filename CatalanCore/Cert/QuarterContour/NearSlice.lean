module
public import CatalanCore.Cert.QuarterContour.FastMacros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.NearSlice
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

/-- The accepted tangent bound with an explicitly supplied, certified near list. -/
def macroLB (near : List Pt) (m : Macro) (b : Quad) : ℚ :=
  SigmaP6.sigTL m.x0 m.y0 m.fd b.1 b.2.1 b.2.2.1 b.2.2.2
    (FastMacros.sigSum b.1 b.2.1 b.2.2.1 b.2.2.2 near)

def rayOK (epsilon : ℚ) (near : List Pt) (mp : ℚ) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b =>
    decide (QuarterCompute.FastNode.boxGeom b) &&
    decide (mp ≤ QuarterCompute.FastNode.quarterBoxLB epsilon (macroLB near m b.1)
      b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2))

lemma macroLB_eq (pts near : List Pt) (m : Macro) (b : Quad)
    (hnear : macroNear pts m = near) :
    macroLB near m b = FastMacros.macroLB pts m b := by
  subst near
  rfl

lemma rayOK_eq_fast (epsilon : ℚ) (pts near : List Pt) (mp : ℚ) (m : Macro)
    (hnear : macroNear pts m = near) :
    rayOK epsilon near mp m = FastMacros.rayOK epsilon pts mp m := by
  subst near
  rfl

lemma rayOK_eq (epsilon : ℚ) (pts near : List Pt) (mp : ℚ) (m : Macro)
    (hnear : macroNear pts m = near) :
    rayOK epsilon near mp m = QuarterContour.rayOK epsilon pts mp m :=
  (rayOK_eq_fast epsilon pts near mp m hnear).trans (FastMacros.rayOK_eq epsilon pts mp m)
end CatalanCore.Cert.QuarterContour.NearSlice
#print axioms CatalanCore.Cert.QuarterContour.NearSlice.rayOK_eq
