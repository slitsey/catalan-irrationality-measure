module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray432
public import CatalanCore.Cert.SigmaQuarter.Ray433
public import CatalanCore.Cert.SigmaQuarter.Ray434
public import CatalanCore.Cert.SigmaQuarter.Ray435
public import CatalanCore.Cert.SigmaQuarter.Ray436
public import CatalanCore.Cert.SigmaQuarter.Ray437
public import CatalanCore.Cert.SigmaQuarter.Ray438
public import CatalanCore.Cert.SigmaQuarter.Ray439

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo54 : List Macro := Ray432Data ++ Ray433Data ++ Ray434Data ++ Ray435Data ++ Ray436Data ++ Ray437Data ++ Ray438Data ++ Ray439Data
theorem rayGeo54_shape : (boxes rayGeo54).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo54_cover : IntervalCovers (rayIntervals rayGeo54) (15321 / 131072 : ℚ) (15705 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
