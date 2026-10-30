module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray288
public import CatalanCore.Cert.SigmaQuarter.Ray289
public import CatalanCore.Cert.SigmaQuarter.Ray290
public import CatalanCore.Cert.SigmaQuarter.Ray291
public import CatalanCore.Cert.SigmaQuarter.Ray292
public import CatalanCore.Cert.SigmaQuarter.Ray293
public import CatalanCore.Cert.SigmaQuarter.Ray294
public import CatalanCore.Cert.SigmaQuarter.Ray295

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo36 : List Macro := Ray288Data ++ Ray289Data ++ Ray290Data ++ Ray291Data ++ Ray292Data ++ Ray293Data ++ Ray294Data ++ Ray295Data
theorem rayGeo36_shape : (boxes rayGeo36).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo36_cover : IntervalCovers (rayIntervals rayGeo36) (34023 / 524288 : ℚ) (35301 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
