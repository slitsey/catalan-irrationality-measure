module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg56
public import CatalanCore.Cert.SigmaQuarter.Seg57
public import CatalanCore.Cert.SigmaQuarter.Seg58
public import CatalanCore.Cert.SigmaQuarter.Seg59
public import CatalanCore.Cert.SigmaQuarter.Seg60
public import CatalanCore.Cert.SigmaQuarter.Seg61
public import CatalanCore.Cert.SigmaQuarter.Seg62
public import CatalanCore.Cert.SigmaQuarter.Seg63

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo7 : List Macro := Seg56Data ++ Seg57Data ++ Seg58Data ++ Seg59Data ++ Seg60Data ++ Seg61Data ++ Seg62Data ++ Seg63Data
theorem segGeo7_shape : (boxes segGeo7).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo7_cover : IntervalCovers (intervals segGeo7) (-14173392077 / 1099511627776 : ℚ) (-1073741825 / 1099511627776 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo7_cost : ((boxes segGeo7).map segCost).sum = (-24562569028810497315379 / 2951479051793528258560000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
