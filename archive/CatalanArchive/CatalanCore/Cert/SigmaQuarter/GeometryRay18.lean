module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray144
public import CatalanCore.Cert.SigmaQuarter.Ray145
public import CatalanCore.Cert.SigmaQuarter.Ray146
public import CatalanCore.Cert.SigmaQuarter.Ray147
public import CatalanCore.Cert.SigmaQuarter.Ray148
public import CatalanCore.Cert.SigmaQuarter.Ray149
public import CatalanCore.Cert.SigmaQuarter.Ray150
public import CatalanCore.Cert.SigmaQuarter.Ray151

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo18 : List Macro := Ray144Data ++ Ray145Data ++ Ray146Data ++ Ray147Data ++ Ray148Data ++ Ray149Data ++ Ray150Data ++ Ray151Data
theorem rayGeo18_shape : (boxes rayGeo18).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo18_cover : IntervalCovers (rayIntervals rayGeo18) (15567 / 524288 : ℚ) (32985 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
