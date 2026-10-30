module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray264
public import CatalanCore.Cert.SigmaQuarter.Ray265
public import CatalanCore.Cert.SigmaQuarter.Ray266
public import CatalanCore.Cert.SigmaQuarter.Ray267
public import CatalanCore.Cert.SigmaQuarter.Ray268
public import CatalanCore.Cert.SigmaQuarter.Ray269
public import CatalanCore.Cert.SigmaQuarter.Ray270
public import CatalanCore.Cert.SigmaQuarter.Ray271

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo33 : List Macro := Ray264Data ++ Ray265Data ++ Ray266Data ++ Ray267Data ++ Ray268Data ++ Ray269Data ++ Ray270Data ++ Ray271Data
theorem rayGeo33_shape : (boxes rayGeo33).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo33_cover : IntervalCovers (rayIntervals rayGeo33) (7623 / 131072 : ℚ) (1977 / 32768 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
