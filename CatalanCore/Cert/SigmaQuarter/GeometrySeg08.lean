module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg64

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo8 : List Macro := Seg64Data
theorem segGeo8_shape : (boxes segGeo8).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo8_cover : IntervalCovers (intervals segGeo8) (-1073741825 / 1099511627776 : ℚ) (0 / 1 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo8_cost : ((boxes segGeo8).map segCost).sum = (-47477273718547407023 / 59029581035870565171200 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
