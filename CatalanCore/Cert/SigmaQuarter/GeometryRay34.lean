module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray272
public import CatalanCore.Cert.SigmaQuarter.Ray273
public import CatalanCore.Cert.SigmaQuarter.Ray274
public import CatalanCore.Cert.SigmaQuarter.Ray275
public import CatalanCore.Cert.SigmaQuarter.Ray276
public import CatalanCore.Cert.SigmaQuarter.Ray277
public import CatalanCore.Cert.SigmaQuarter.Ray278
public import CatalanCore.Cert.SigmaQuarter.Ray279

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo34 : List Macro := Ray272Data ++ Ray273Data ++ Ray274Data ++ Ray275Data ++ Ray276Data ++ Ray277Data ++ Ray278Data ++ Ray279Data
theorem rayGeo34_shape : (boxes rayGeo34).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo34_cover : IntervalCovers (rayIntervals rayGeo34) (1977 / 32768 : ℚ) (32799 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
