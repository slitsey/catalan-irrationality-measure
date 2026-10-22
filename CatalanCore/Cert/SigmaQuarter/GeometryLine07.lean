module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line56
public import CatalanCore.Cert.SigmaQuarter.Line57
public import CatalanCore.Cert.SigmaQuarter.Line58
public import CatalanCore.Cert.SigmaQuarter.Line59
public import CatalanCore.Cert.SigmaQuarter.Line60
public import CatalanCore.Cert.SigmaQuarter.Line61
public import CatalanCore.Cert.SigmaQuarter.Line62
public import CatalanCore.Cert.SigmaQuarter.Line63

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo7 : List Macro := Line56Data ++ Line57Data ++ Line58Data ++ Line59Data ++ Line60Data ++ Line61Data ++ Line62Data ++ Line63Data
theorem lineGeo7_shape : (boxes lineGeo7).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo7_cover : IntervalCovers (intervals lineGeo7) (1949 / 2048 : ℚ) (503 / 512 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
