module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray192
public import CatalanCore.Cert.SigmaQuarter.Ray193
public import CatalanCore.Cert.SigmaQuarter.Ray194
public import CatalanCore.Cert.SigmaQuarter.Ray195
public import CatalanCore.Cert.SigmaQuarter.Ray196
public import CatalanCore.Cert.SigmaQuarter.Ray197
public import CatalanCore.Cert.SigmaQuarter.Ray198
public import CatalanCore.Cert.SigmaQuarter.Ray199

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo24 : List Macro := Ray192Data ++ Ray193Data ++ Ray194Data ++ Ray195Data ++ Ray196Data ++ Ray197Data ++ Ray198Data ++ Ray199Data
theorem rayGeo24_shape : (boxes rayGeo24).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo24_cover : IntervalCovers (rayIntervals rayGeo24) (42369 / 1048576 : ℚ) (44319 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
