module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray256
public import CatalanCore.Cert.SigmaQuarter.Ray257
public import CatalanCore.Cert.SigmaQuarter.Ray258
public import CatalanCore.Cert.SigmaQuarter.Ray259
public import CatalanCore.Cert.SigmaQuarter.Ray260
public import CatalanCore.Cert.SigmaQuarter.Ray261
public import CatalanCore.Cert.SigmaQuarter.Ray262
public import CatalanCore.Cert.SigmaQuarter.Ray263

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo32 : List Macro := Ray256Data ++ Ray257Data ++ Ray258Data ++ Ray259Data ++ Ray260Data ++ Ray261Data ++ Ray262Data ++ Ray263Data
theorem rayGeo32_shape : (boxes rayGeo32).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo32_cover : IntervalCovers (rayIntervals rayGeo32) (29391 / 524288 : ℚ) (7623 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
