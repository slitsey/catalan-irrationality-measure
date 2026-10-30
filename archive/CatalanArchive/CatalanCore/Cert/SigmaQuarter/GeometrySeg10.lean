module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg80
public import CatalanCore.Cert.SigmaQuarter.Seg81
public import CatalanCore.Cert.SigmaQuarter.Seg82
public import CatalanCore.Cert.SigmaQuarter.Seg83
public import CatalanCore.Cert.SigmaQuarter.Seg84
public import CatalanCore.Cert.SigmaQuarter.Seg85
public import CatalanCore.Cert.SigmaQuarter.Seg86

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo10 : List Macro := Seg80Data ++ Seg81Data ++ Seg82Data ++ Seg83Data ++ Seg84Data ++ Seg85Data ++ Seg86Data
theorem segGeo10_shape : (boxes segGeo10).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo10_cover : IntervalCovers (intervals segGeo10) (-3972844749 / 549755813888 : ℚ) (0 / 1 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo10_cost : ((boxes segGeo10).map segCost).sum = (-81674377235902213020311 / 14757395258967641292800000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
