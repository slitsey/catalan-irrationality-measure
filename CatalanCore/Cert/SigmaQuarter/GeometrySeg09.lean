module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg72
public import CatalanCore.Cert.SigmaQuarter.Seg73
public import CatalanCore.Cert.SigmaQuarter.Seg74
public import CatalanCore.Cert.SigmaQuarter.Seg75
public import CatalanCore.Cert.SigmaQuarter.Seg76
public import CatalanCore.Cert.SigmaQuarter.Seg77
public import CatalanCore.Cert.SigmaQuarter.Seg78
public import CatalanCore.Cert.SigmaQuarter.Seg79

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo9 : List Macro := Seg72Data ++ Seg73Data ++ Seg74Data ++ Seg75Data ++ Seg76Data ++ Seg77Data ++ Seg78Data ++ Seg79Data
theorem segGeo9_shape : (boxes segGeo9).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo9_cover : IntervalCovers (intervals segGeo9) (-18253611009 / 1099511627776 : ℚ) (-3972844749 / 549755813888 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo9_cost : ((boxes segGeo9).map segCost).sum = (-86683941405863659907977 / 14757395258967641292800000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
