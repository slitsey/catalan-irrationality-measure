module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line64

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo8 : List Macro := Line64Data
theorem lineGeo8_shape : (boxes lineGeo8).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo8_cover : IntervalCovers (intervals lineGeo8) (503 / 512 : ℚ) (1 / 1 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
