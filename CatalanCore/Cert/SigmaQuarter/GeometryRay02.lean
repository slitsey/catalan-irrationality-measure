module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray16
public import CatalanCore.Cert.SigmaQuarter.Ray17
public import CatalanCore.Cert.SigmaQuarter.Ray18
public import CatalanCore.Cert.SigmaQuarter.Ray19
public import CatalanCore.Cert.SigmaQuarter.Ray20
public import CatalanCore.Cert.SigmaQuarter.Ray21
public import CatalanCore.Cert.SigmaQuarter.Ray22
public import CatalanCore.Cert.SigmaQuarter.Ray23

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo2 : List Macro := Ray16Data ++ Ray17Data ++ Ray18Data ++ Ray19Data ++ Ray20Data ++ Ray21Data ++ Ray22Data ++ Ray23Data
theorem rayGeo2_shape : (boxes rayGeo2).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo2_cover : IntervalCovers (rayIntervals rayGeo2) (6411 / 524288 : ℚ) (3003 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
