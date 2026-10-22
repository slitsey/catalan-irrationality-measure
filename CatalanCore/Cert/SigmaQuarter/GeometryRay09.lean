module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray72
public import CatalanCore.Cert.SigmaQuarter.Ray73
public import CatalanCore.Cert.SigmaQuarter.Ray74
public import CatalanCore.Cert.SigmaQuarter.Ray75
public import CatalanCore.Cert.SigmaQuarter.Ray76
public import CatalanCore.Cert.SigmaQuarter.Ray77
public import CatalanCore.Cert.SigmaQuarter.Ray78
public import CatalanCore.Cert.SigmaQuarter.Ray79

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo9 : List Macro := Ray72Data ++ Ray73Data ++ Ray74Data ++ Ray75Data ++ Ray76Data ++ Ray77Data ++ Ray78Data ++ Ray79Data
theorem rayGeo9_shape : (boxes rayGeo9).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo9_cover : IntervalCovers (rayIntervals rayGeo9) (7671 / 524288 : ℚ) (8523 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
