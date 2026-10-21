module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg48
public import CatalanCore.Cert.SigmaQuarter.Seg49
public import CatalanCore.Cert.SigmaQuarter.Seg50
public import CatalanCore.Cert.SigmaQuarter.Seg51
public import CatalanCore.Cert.SigmaQuarter.Seg52
public import CatalanCore.Cert.SigmaQuarter.Seg53
public import CatalanCore.Cert.SigmaQuarter.Seg54
public import CatalanCore.Cert.SigmaQuarter.Seg55

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo6 : List Macro := Seg48Data ++ Seg49Data ++ Seg50Data ++ Seg51Data ++ Seg52Data ++ Seg53Data ++ Seg54Data ++ Seg55Data
theorem segGeo6_shape : (boxes segGeo6).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo6_cover : IntervalCovers (intervals segGeo6) (-27917287425 / 1099511627776 : ℚ) (-14173392077 / 1099511627776 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo6_cost : ((boxes segGeo6).map segCost).sum = (-9612988331239633283223 / 1475739525896764129280000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
