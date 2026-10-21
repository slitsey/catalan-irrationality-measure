module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray8
public import CatalanCore.Cert.SigmaQuarter.Ray9
public import CatalanCore.Cert.SigmaQuarter.Ray10
public import CatalanCore.Cert.SigmaQuarter.Ray11
public import CatalanCore.Cert.SigmaQuarter.Ray12
public import CatalanCore.Cert.SigmaQuarter.Ray13
public import CatalanCore.Cert.SigmaQuarter.Ray14
public import CatalanCore.Cert.SigmaQuarter.Ray15

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo1 : List Macro := Ray8Data ++ Ray9Data ++ Ray10Data ++ Ray11Data ++ Ray12Data ++ Ray13Data ++ Ray14Data ++ Ray15Data
theorem rayGeo1_shape : (boxes rayGeo1).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo1_cover : IntervalCovers (rayIntervals rayGeo1) (1227 / 262144 : ℚ) (6411 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
