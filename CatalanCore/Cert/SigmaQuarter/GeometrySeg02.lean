module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg16
public import CatalanCore.Cert.SigmaQuarter.Seg17
public import CatalanCore.Cert.SigmaQuarter.Seg18
public import CatalanCore.Cert.SigmaQuarter.Seg19
public import CatalanCore.Cert.SigmaQuarter.Seg20
public import CatalanCore.Cert.SigmaQuarter.Seg21
public import CatalanCore.Cert.SigmaQuarter.Seg22
public import CatalanCore.Cert.SigmaQuarter.Seg23

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo2 : List Macro := Seg16Data ++ Seg17Data ++ Seg18Data ++ Seg19Data ++ Seg20Data ++ Seg21Data ++ Seg22Data ++ Seg23Data
theorem segGeo2_shape : (boxes segGeo2).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo2_cover : IntervalCovers (intervals segGeo2) (-41446434407 / 549755813888 : ℚ) (-34574486733 / 549755813888 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo2_cost : ((boxes segGeo2).map segCost).sum = (-3015968931549397604571 / 2951479051793528258560000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
