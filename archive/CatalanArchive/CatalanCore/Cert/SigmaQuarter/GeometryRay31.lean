module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray248
public import CatalanCore.Cert.SigmaQuarter.Ray249
public import CatalanCore.Cert.SigmaQuarter.Ray250
public import CatalanCore.Cert.SigmaQuarter.Ray251
public import CatalanCore.Cert.SigmaQuarter.Ray252
public import CatalanCore.Cert.SigmaQuarter.Ray253
public import CatalanCore.Cert.SigmaQuarter.Ray254
public import CatalanCore.Cert.SigmaQuarter.Ray255

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo31 : List Macro := Ray248Data ++ Ray249Data ++ Ray250Data ++ Ray251Data ++ Ray252Data ++ Ray253Data ++ Ray254Data ++ Ray255Data
theorem rayGeo31_shape : (boxes rayGeo31).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo31_cover : IntervalCovers (rayIntervals rayGeo31) (56607 / 1048576 : ℚ) (29391 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
