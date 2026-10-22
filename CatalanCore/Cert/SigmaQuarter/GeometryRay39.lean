module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray312
public import CatalanCore.Cert.SigmaQuarter.Ray313
public import CatalanCore.Cert.SigmaQuarter.Ray314
public import CatalanCore.Cert.SigmaQuarter.Ray315
public import CatalanCore.Cert.SigmaQuarter.Ray316
public import CatalanCore.Cert.SigmaQuarter.Ray317
public import CatalanCore.Cert.SigmaQuarter.Ray318
public import CatalanCore.Cert.SigmaQuarter.Ray319

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo39 : List Macro := Ray312Data ++ Ray313Data ++ Ray314Data ++ Ray315Data ++ Ray316Data ++ Ray317Data ++ Ray318Data ++ Ray319Data
theorem rayGeo39_shape : (boxes rayGeo39).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo39_cover : IntervalCovers (rayIntervals rayGeo39) (9561 / 131072 : ℚ) (9945 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
