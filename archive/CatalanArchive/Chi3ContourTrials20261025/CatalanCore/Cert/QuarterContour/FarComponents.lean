module
public import CatalanCore.Cert.QuarterContour.FastMacros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FarComponents
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

theorem fd_eq_of_components (a b : FD)
    (h0 : a.1 = b.1) (h1 : a.2.1 = b.2.1) (h2 : a.2.2.1 = b.2.2.1)
    (h3 : a.2.2.2.1 = b.2.2.2.1) (h4 : a.2.2.2.2.1 = b.2.2.2.2.1)
    (h5 : a.2.2.2.2.2 = b.2.2.2.2.2) : a = b :=
  Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5))))

theorem farOK_of_components (pts : List Pt) (m : Macro)
    (h0 : (FastMacros.farSum m.x0 m.y0 (macroFar pts m)).1 = m.fd.1)
    (h1 : (FastMacros.farSum m.x0 m.y0 (macroFar pts m)).2.1 = m.fd.2.1)
    (h2 : (FastMacros.farSum m.x0 m.y0 (macroFar pts m)).2.2.1 = m.fd.2.2.1)
    (h3 : (FastMacros.farSum m.x0 m.y0 (macroFar pts m)).2.2.2.1 = m.fd.2.2.2.1)
    (h4 : (FastMacros.farSum m.x0 m.y0 (macroFar pts m)).2.2.2.2.1 = m.fd.2.2.2.2.1)
    (h5 : (FastMacros.farSum m.x0 m.y0 (macroFar pts m)).2.2.2.2.2 = m.fd.2.2.2.2.2) :
    SigmaQuarter.farOK pts m := by
  rw [← FastMacros.farOK_eq]
  exact fd_eq_of_components _ _ h0 h1 h2 h3 h4 h5
end CatalanCore.Cert.QuarterContour.FarComponents
#print axioms CatalanCore.Cert.QuarterContour.FarComponents.farOK_of_components
