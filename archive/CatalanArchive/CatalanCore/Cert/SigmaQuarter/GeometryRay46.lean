module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray368
public import CatalanCore.Cert.SigmaQuarter.Ray369
public import CatalanCore.Cert.SigmaQuarter.Ray370
public import CatalanCore.Cert.SigmaQuarter.Ray371
public import CatalanCore.Cert.SigmaQuarter.Ray372
public import CatalanCore.Cert.SigmaQuarter.Ray373
public import CatalanCore.Cert.SigmaQuarter.Ray374
public import CatalanCore.Cert.SigmaQuarter.Ray375

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo46 : List Macro := Ray368Data ++ Ray369Data ++ Ray370Data ++ Ray371Data ++ Ray372Data ++ Ray373Data ++ Ray374Data ++ Ray375Data
theorem rayGeo46_shape : (boxes rayGeo46).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo46_cover : IntervalCovers (rayIntervals rayGeo46) (12249 / 131072 : ℚ) (12633 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
