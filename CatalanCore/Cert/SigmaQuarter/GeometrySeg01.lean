module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg8
public import CatalanCore.Cert.SigmaQuarter.Seg9
public import CatalanCore.Cert.SigmaQuarter.Seg10
public import CatalanCore.Cert.SigmaQuarter.Seg11
public import CatalanCore.Cert.SigmaQuarter.Seg12
public import CatalanCore.Cert.SigmaQuarter.Seg13
public import CatalanCore.Cert.SigmaQuarter.Seg14
public import CatalanCore.Cert.SigmaQuarter.Seg15

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo1 : List Macro := Seg8Data ++ Seg9Data ++ Seg10Data ++ Seg11Data ++ Seg12Data ++ Seg13Data ++ Seg14Data ++ Seg15Data
theorem segGeo1_shape : (boxes segGeo1).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo1_cover : IntervalCovers (intervals segGeo1) (-96636764161 / 1099511627776 : ℚ) (-41446434407 / 549755813888 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo1_cost : ((boxes segGeo1).map segCost).sum = (-825458241549123639319 / 2951479051793528258560000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
