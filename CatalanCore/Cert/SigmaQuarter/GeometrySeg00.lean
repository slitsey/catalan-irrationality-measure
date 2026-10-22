module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg0
public import CatalanCore.Cert.SigmaQuarter.Seg1
public import CatalanCore.Cert.SigmaQuarter.Seg2
public import CatalanCore.Cert.SigmaQuarter.Seg3
public import CatalanCore.Cert.SigmaQuarter.Seg4
public import CatalanCore.Cert.SigmaQuarter.Seg5
public import CatalanCore.Cert.SigmaQuarter.Seg6
public import CatalanCore.Cert.SigmaQuarter.Seg7

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo0 : List Macro := Seg0Data ++ Seg1Data ++ Seg2Data ++ Seg3Data ++ Seg4Data ++ Seg5Data ++ Seg6Data ++ Seg7Data
theorem segGeo0_shape : (boxes segGeo0).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo0_cover : IntervalCovers (intervals segGeo0) (-54975581389 / 549755813888 : ℚ) (-25179245773 / 274877906944 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo0_cost : ((boxes segGeo0).map segCost).sum = (0 / 1 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
