module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg40
public import CatalanCore.Cert.SigmaQuarter.Seg41
public import CatalanCore.Cert.SigmaQuarter.Seg42
public import CatalanCore.Cert.SigmaQuarter.Seg43
public import CatalanCore.Cert.SigmaQuarter.Seg44
public import CatalanCore.Cert.SigmaQuarter.Seg45
public import CatalanCore.Cert.SigmaQuarter.Seg46
public import CatalanCore.Cert.SigmaQuarter.Seg47

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo5 : List Macro := Seg40Data ++ Seg41Data ++ Seg42Data ++ Seg43Data ++ Seg44Data ++ Seg45Data ++ Seg46Data ++ Seg47Data
theorem segGeo5_shape : (boxes segGeo5).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo5_cover : IntervalCovers (intervals segGeo5) (-29742648525 / 549755813888 : ℚ) (-12294343885 / 274877906944 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo5_cost : ((boxes segGeo5).map segCost).sum = (-6150229774095453423789 / 2951479051793528258560000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
