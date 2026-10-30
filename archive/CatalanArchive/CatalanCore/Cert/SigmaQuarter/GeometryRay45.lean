module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray360
public import CatalanCore.Cert.SigmaQuarter.Ray361
public import CatalanCore.Cert.SigmaQuarter.Ray362
public import CatalanCore.Cert.SigmaQuarter.Ray363
public import CatalanCore.Cert.SigmaQuarter.Ray364
public import CatalanCore.Cert.SigmaQuarter.Ray365
public import CatalanCore.Cert.SigmaQuarter.Ray366
public import CatalanCore.Cert.SigmaQuarter.Ray367

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo45 : List Macro := Ray360Data ++ Ray361Data ++ Ray362Data ++ Ray363Data ++ Ray364Data ++ Ray365Data ++ Ray366Data ++ Ray367Data
theorem rayGeo45_shape : (boxes rayGeo45).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo45_cover : IntervalCovers (rayIntervals rayGeo45) (11865 / 131072 : ℚ) (12249 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
