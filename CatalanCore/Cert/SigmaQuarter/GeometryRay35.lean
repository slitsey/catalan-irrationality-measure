module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray280
public import CatalanCore.Cert.SigmaQuarter.Ray281
public import CatalanCore.Cert.SigmaQuarter.Ray282
public import CatalanCore.Cert.SigmaQuarter.Ray283
public import CatalanCore.Cert.SigmaQuarter.Ray284
public import CatalanCore.Cert.SigmaQuarter.Ray285
public import CatalanCore.Cert.SigmaQuarter.Ray286
public import CatalanCore.Cert.SigmaQuarter.Ray287

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo35 : List Macro := Ray280Data ++ Ray281Data ++ Ray282Data ++ Ray283Data ++ Ray284Data ++ Ray285Data ++ Ray286Data ++ Ray287Data
theorem rayGeo35_shape : (boxes rayGeo35).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo35_cover : IntervalCovers (rayIntervals rayGeo35) (32799 / 524288 : ℚ) (34023 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
