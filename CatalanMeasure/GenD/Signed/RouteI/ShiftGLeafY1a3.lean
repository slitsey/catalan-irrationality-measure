module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf

@[expose] public section

/-!
# G5 shiftG, leaf Y1a, quarter 3: `checkZ` on the cell `[3/4, (3+1)/4]` for the knot `γ = 11/50`
(first population, `dv24`).  One quarter of the 219-cell kernel decision of `Y1_11_50`, split so each module
stays inside a few GB.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a3
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf OAI.InternalCatalan

noncomputable section

theorem Y1_11_50_q3_check : checkZ (addL (combZ (14224759 * 2 ^ 24 * 5354228880 * 4 ^ 65 * L64 * 50)
    (wts (-2 * 4 ^ 65 * L64 * 50 * 10 ^ 8) 5354228880 dv24) [])
    (smulL (-(11 * 2 ^ 24 * 5354228880 * 10 ^ 8)) (0 :: logW))) 12 3 2 = true := by
  decide +kernel -- kcost: 49.6 s measured (standalone profiler), quarter of 219 cellOK calls (mirror), degree 66

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a3
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1a3.Y1_11_50_q3_check
