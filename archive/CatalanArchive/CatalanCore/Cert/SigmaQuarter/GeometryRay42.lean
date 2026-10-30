module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray336
public import CatalanCore.Cert.SigmaQuarter.Ray337
public import CatalanCore.Cert.SigmaQuarter.Ray338
public import CatalanCore.Cert.SigmaQuarter.Ray339
public import CatalanCore.Cert.SigmaQuarter.Ray340
public import CatalanCore.Cert.SigmaQuarter.Ray341
public import CatalanCore.Cert.SigmaQuarter.Ray342
public import CatalanCore.Cert.SigmaQuarter.Ray343

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo42 : List Macro := Ray336Data ++ Ray337Data ++ Ray338Data ++ Ray339Data ++ Ray340Data ++ Ray341Data ++ Ray342Data ++ Ray343Data
theorem rayGeo42_shape : (boxes rayGeo42).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo42_cover : IntervalCovers (rayIntervals rayGeo42) (10713 / 131072 : ℚ) (11097 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
