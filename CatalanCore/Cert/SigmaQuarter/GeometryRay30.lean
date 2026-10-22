module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray240
public import CatalanCore.Cert.SigmaQuarter.Ray241
public import CatalanCore.Cert.SigmaQuarter.Ray242
public import CatalanCore.Cert.SigmaQuarter.Ray243
public import CatalanCore.Cert.SigmaQuarter.Ray244
public import CatalanCore.Cert.SigmaQuarter.Ray245
public import CatalanCore.Cert.SigmaQuarter.Ray246
public import CatalanCore.Cert.SigmaQuarter.Ray247

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo30 : List Macro := Ray240Data ++ Ray241Data ++ Ray242Data ++ Ray243Data ++ Ray244Data ++ Ray245Data ++ Ray246Data ++ Ray247Data
theorem rayGeo30_shape : (boxes rayGeo30).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo30_cover : IntervalCovers (rayIntervals rayGeo30) (27225 / 524288 : ℚ) (56607 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
