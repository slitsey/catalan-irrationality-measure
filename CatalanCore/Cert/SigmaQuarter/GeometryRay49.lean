module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray392
public import CatalanCore.Cert.SigmaQuarter.Ray393
public import CatalanCore.Cert.SigmaQuarter.Ray394
public import CatalanCore.Cert.SigmaQuarter.Ray395
public import CatalanCore.Cert.SigmaQuarter.Ray396
public import CatalanCore.Cert.SigmaQuarter.Ray397
public import CatalanCore.Cert.SigmaQuarter.Ray398
public import CatalanCore.Cert.SigmaQuarter.Ray399

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo49 : List Macro := Ray392Data ++ Ray393Data ++ Ray394Data ++ Ray395Data ++ Ray396Data ++ Ray397Data ++ Ray398Data ++ Ray399Data
theorem rayGeo49_shape : (boxes rayGeo49).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo49_cover : IntervalCovers (rayIntervals rayGeo49) (13401 / 131072 : ℚ) (13785 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
