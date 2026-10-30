module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray416
public import CatalanCore.Cert.SigmaQuarter.Ray417
public import CatalanCore.Cert.SigmaQuarter.Ray418
public import CatalanCore.Cert.SigmaQuarter.Ray419
public import CatalanCore.Cert.SigmaQuarter.Ray420
public import CatalanCore.Cert.SigmaQuarter.Ray421
public import CatalanCore.Cert.SigmaQuarter.Ray422
public import CatalanCore.Cert.SigmaQuarter.Ray423

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo52 : List Macro := Ray416Data ++ Ray417Data ++ Ray418Data ++ Ray419Data ++ Ray420Data ++ Ray421Data ++ Ray422Data ++ Ray423Data
theorem rayGeo52_shape : (boxes rayGeo52).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo52_cover : IntervalCovers (rayIntervals rayGeo52) (14553 / 131072 : ℚ) (14937 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
