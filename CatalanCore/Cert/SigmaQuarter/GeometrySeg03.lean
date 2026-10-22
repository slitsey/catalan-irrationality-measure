module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg24
public import CatalanCore.Cert.SigmaQuarter.Seg25
public import CatalanCore.Cert.SigmaQuarter.Seg26
public import CatalanCore.Cert.SigmaQuarter.Seg27
public import CatalanCore.Cert.SigmaQuarter.Seg28
public import CatalanCore.Cert.SigmaQuarter.Seg29
public import CatalanCore.Cert.SigmaQuarter.Seg30
public import CatalanCore.Cert.SigmaQuarter.Seg31

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo3 : List Macro := Seg24Data ++ Seg25Data ++ Seg26Data ++ Seg27Data ++ Seg28Data ++ Seg29Data ++ Seg30Data ++ Seg31Data
theorem segGeo3_shape : (boxes segGeo3).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo3_cover : IntervalCovers (intervals segGeo3) (-80101140071 / 1099511627776 : ℚ) (-69793218561 / 1099511627776 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo3_cost : ((boxes segGeo3).map segCost).sum = (-1255650998784943365957 / 1475739525896764129280000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
