module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray456
public import CatalanCore.Cert.SigmaQuarter.Ray457
public import CatalanCore.Cert.SigmaQuarter.Ray458
public import CatalanCore.Cert.SigmaQuarter.Ray459
public import CatalanCore.Cert.SigmaQuarter.Ray460
public import CatalanCore.Cert.SigmaQuarter.Ray461
public import CatalanCore.Cert.SigmaQuarter.Ray462
public import CatalanCore.Cert.SigmaQuarter.Ray463

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo57 : List Macro := Ray456Data ++ Ray457Data ++ Ray458Data ++ Ray459Data ++ Ray460Data ++ Ray461Data ++ Ray462Data ++ Ray463Data
theorem rayGeo57_shape : (boxes rayGeo57).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo57_cover : IntervalCovers (rayIntervals rayGeo57) (16473 / 131072 : ℚ) (16857 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
