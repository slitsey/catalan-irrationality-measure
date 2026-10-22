module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray344
public import CatalanCore.Cert.SigmaQuarter.Ray345
public import CatalanCore.Cert.SigmaQuarter.Ray346
public import CatalanCore.Cert.SigmaQuarter.Ray347
public import CatalanCore.Cert.SigmaQuarter.Ray348
public import CatalanCore.Cert.SigmaQuarter.Ray349
public import CatalanCore.Cert.SigmaQuarter.Ray350
public import CatalanCore.Cert.SigmaQuarter.Ray351

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo43 : List Macro := Ray344Data ++ Ray345Data ++ Ray346Data ++ Ray347Data ++ Ray348Data ++ Ray349Data ++ Ray350Data ++ Ray351Data
theorem rayGeo43_shape : (boxes rayGeo43).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo43_cover : IntervalCovers (rayIntervals rayGeo43) (11097 / 131072 : ℚ) (11481 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
