module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg64
public import CatalanCore.Cert.SigmaQuarter.Seg65
public import CatalanCore.Cert.SigmaQuarter.Seg66
public import CatalanCore.Cert.SigmaQuarter.Seg67
public import CatalanCore.Cert.SigmaQuarter.Seg68
public import CatalanCore.Cert.SigmaQuarter.Seg69
public import CatalanCore.Cert.SigmaQuarter.Seg70
public import CatalanCore.Cert.SigmaQuarter.Seg71

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo8 : List Macro := Seg64Data ++ Seg65Data ++ Seg66Data ++ Seg67Data ++ Seg68Data ++ Seg69Data ++ Seg70Data ++ Seg71Data
theorem segGeo8_shape : (boxes segGeo8).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo8_cover : IntervalCovers (intervals segGeo8) (-28561532519 / 1099511627776 : ℚ) (-18253611009 / 1099511627776 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo8_cost : ((boxes segGeo8).map segCost).sum = (-1734585987840642700083 / 368934881474191032320000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
