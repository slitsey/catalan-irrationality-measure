module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray384
public import CatalanCore.Cert.SigmaQuarter.Ray385
public import CatalanCore.Cert.SigmaQuarter.Ray386
public import CatalanCore.Cert.SigmaQuarter.Ray387
public import CatalanCore.Cert.SigmaQuarter.Ray388
public import CatalanCore.Cert.SigmaQuarter.Ray389
public import CatalanCore.Cert.SigmaQuarter.Ray390
public import CatalanCore.Cert.SigmaQuarter.Ray391

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo48 : List Macro := Ray384Data ++ Ray385Data ++ Ray386Data ++ Ray387Data ++ Ray388Data ++ Ray389Data ++ Ray390Data ++ Ray391Data
theorem rayGeo48_shape : (boxes rayGeo48).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo48_cover : IntervalCovers (rayIntervals rayGeo48) (13017 / 131072 : ℚ) (13401 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
