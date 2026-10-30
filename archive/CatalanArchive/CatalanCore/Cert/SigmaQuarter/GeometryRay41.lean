module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray328
public import CatalanCore.Cert.SigmaQuarter.Ray329
public import CatalanCore.Cert.SigmaQuarter.Ray330
public import CatalanCore.Cert.SigmaQuarter.Ray331
public import CatalanCore.Cert.SigmaQuarter.Ray332
public import CatalanCore.Cert.SigmaQuarter.Ray333
public import CatalanCore.Cert.SigmaQuarter.Ray334
public import CatalanCore.Cert.SigmaQuarter.Ray335

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo41 : List Macro := Ray328Data ++ Ray329Data ++ Ray330Data ++ Ray331Data ++ Ray332Data ++ Ray333Data ++ Ray334Data ++ Ray335Data
theorem rayGeo41_shape : (boxes rayGeo41).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo41_cover : IntervalCovers (rayIntervals rayGeo41) (10329 / 131072 : ℚ) (10713 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
