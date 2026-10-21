module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line64
public import CatalanCore.Cert.SigmaQuarter.Line65
public import CatalanCore.Cert.SigmaQuarter.Line66
public import CatalanCore.Cert.SigmaQuarter.Line67
public import CatalanCore.Cert.SigmaQuarter.Line68
public import CatalanCore.Cert.SigmaQuarter.Line69
public import CatalanCore.Cert.SigmaQuarter.Line70
public import CatalanCore.Cert.SigmaQuarter.Line71

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo8 : List Macro := Line64Data ++ Line65Data ++ Line66Data ++ Line67Data ++ Line68Data ++ Line69Data ++ Line70Data ++ Line71Data
theorem lineGeo8_shape : (boxes lineGeo8).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo8_cover : IntervalCovers (intervals lineGeo8) (7319 / 8192 : ℚ) (239 / 256 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
