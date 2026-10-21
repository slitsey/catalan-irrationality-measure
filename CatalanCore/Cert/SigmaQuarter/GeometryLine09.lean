module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line72
public import CatalanCore.Cert.SigmaQuarter.Line73

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo9 : List Macro := Line72Data ++ Line73Data
theorem lineGeo9_shape : (boxes lineGeo9).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo9_cover : IntervalCovers (intervals lineGeo9) (239 / 256 : ℚ) (1 / 1 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
