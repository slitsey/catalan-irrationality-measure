module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray120
public import CatalanCore.Cert.SigmaQuarter.Ray121
public import CatalanCore.Cert.SigmaQuarter.Ray122
public import CatalanCore.Cert.SigmaQuarter.Ray123
public import CatalanCore.Cert.SigmaQuarter.Ray124
public import CatalanCore.Cert.SigmaQuarter.Ray125
public import CatalanCore.Cert.SigmaQuarter.Ray126
public import CatalanCore.Cert.SigmaQuarter.Ray127

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo15 : List Macro := Ray120Data ++ Ray121Data ++ Ray122Data ++ Ray123Data ++ Ray124Data ++ Ray125Data ++ Ray126Data ++ Ray127Data
theorem rayGeo15_shape : (boxes rayGeo15).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo15_cover : IntervalCovers (rayIntervals rayGeo15) (12879 / 524288 : ℚ) (13761 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
