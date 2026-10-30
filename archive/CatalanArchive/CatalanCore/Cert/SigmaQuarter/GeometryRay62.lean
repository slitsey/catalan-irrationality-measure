module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray496

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo62 : List Macro := Ray496Data
theorem rayGeo62_shape : (boxes rayGeo62).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo62_cover : IntervalCovers (rayIntervals rayGeo62) (579 / 512 : ℚ) (3 / 2 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
