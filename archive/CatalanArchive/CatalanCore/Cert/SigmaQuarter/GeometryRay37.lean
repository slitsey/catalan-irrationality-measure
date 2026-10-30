module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray296
public import CatalanCore.Cert.SigmaQuarter.Ray297
public import CatalanCore.Cert.SigmaQuarter.Ray298
public import CatalanCore.Cert.SigmaQuarter.Ray299
public import CatalanCore.Cert.SigmaQuarter.Ray300
public import CatalanCore.Cert.SigmaQuarter.Ray301
public import CatalanCore.Cert.SigmaQuarter.Ray302
public import CatalanCore.Cert.SigmaQuarter.Ray303

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo37 : List Macro := Ray296Data ++ Ray297Data ++ Ray298Data ++ Ray299Data ++ Ray300Data ++ Ray301Data ++ Ray302Data ++ Ray303Data
theorem rayGeo37_shape : (boxes rayGeo37).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo37_cover : IntervalCovers (rayIntervals rayGeo37) (35301 / 524288 : ℚ) (9177 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
