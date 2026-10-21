module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line48
public import CatalanCore.Cert.SigmaQuarter.Line49
public import CatalanCore.Cert.SigmaQuarter.Line50
public import CatalanCore.Cert.SigmaQuarter.Line51
public import CatalanCore.Cert.SigmaQuarter.Line52
public import CatalanCore.Cert.SigmaQuarter.Line53
public import CatalanCore.Cert.SigmaQuarter.Line54
public import CatalanCore.Cert.SigmaQuarter.Line55

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo6 : List Macro := Line48Data ++ Line49Data ++ Line50Data ++ Line51Data ++ Line52Data ++ Line53Data ++ Line54Data ++ Line55Data
theorem lineGeo6_shape : (boxes lineGeo6).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo6_cover : IntervalCovers (intervals lineGeo6) (29003 / 32768 : ℚ) (7273 / 8192 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
