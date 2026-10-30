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
theorem segGeo6_cover : IntervalCovers (intervals segGeo6) (-12294343885 / 274877906944 : ℚ) (-38869454029 / 1099511627776 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo6_cost : ((boxes segGeo6).map segCost).sum = (-20978151682666094318051 / 7378697629483820646400000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
