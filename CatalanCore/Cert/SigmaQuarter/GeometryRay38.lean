module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray304
public import CatalanCore.Cert.SigmaQuarter.Ray305
public import CatalanCore.Cert.SigmaQuarter.Ray306
public import CatalanCore.Cert.SigmaQuarter.Ray307
public import CatalanCore.Cert.SigmaQuarter.Ray308
public import CatalanCore.Cert.SigmaQuarter.Ray309
public import CatalanCore.Cert.SigmaQuarter.Ray310
public import CatalanCore.Cert.SigmaQuarter.Ray311

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo38 : List Macro := Ray304Data ++ Ray305Data ++ Ray306Data ++ Ray307Data ++ Ray308Data ++ Ray309Data ++ Ray310Data ++ Ray311Data
theorem rayGeo38_shape : (boxes rayGeo38).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo38_cover : IntervalCovers (rayIntervals rayGeo38) (9177 / 131072 : ℚ) (9561 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
