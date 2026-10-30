module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray320
public import CatalanCore.Cert.SigmaQuarter.Ray321
public import CatalanCore.Cert.SigmaQuarter.Ray322
public import CatalanCore.Cert.SigmaQuarter.Ray323
public import CatalanCore.Cert.SigmaQuarter.Ray324
public import CatalanCore.Cert.SigmaQuarter.Ray325
public import CatalanCore.Cert.SigmaQuarter.Ray326
public import CatalanCore.Cert.SigmaQuarter.Ray327

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo40 : List Macro := Ray320Data ++ Ray321Data ++ Ray322Data ++ Ray323Data ++ Ray324Data ++ Ray325Data ++ Ray326Data ++ Ray327Data
theorem rayGeo40_shape : (boxes rayGeo40).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo40_cover : IntervalCovers (rayIntervals rayGeo40) (9945 / 131072 : ℚ) (10329 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
