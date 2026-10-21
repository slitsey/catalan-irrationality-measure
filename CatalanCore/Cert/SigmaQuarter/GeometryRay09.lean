module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray72
public import CatalanCore.Cert.SigmaQuarter.Ray73
public import CatalanCore.Cert.SigmaQuarter.Ray74

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo9 : List Macro := Ray72Data ++ Ray73Data ++ Ray74Data
theorem rayGeo9_shape : (boxes rayGeo9).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo9_cover : IntervalCovers (rayIntervals rayGeo9) (87 / 512 : ℚ) (3 / 2 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
