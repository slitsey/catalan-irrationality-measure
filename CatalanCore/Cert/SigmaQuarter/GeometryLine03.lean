module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line24
public import CatalanCore.Cert.SigmaQuarter.Line25
public import CatalanCore.Cert.SigmaQuarter.Line26
public import CatalanCore.Cert.SigmaQuarter.Line27
public import CatalanCore.Cert.SigmaQuarter.Line28
public import CatalanCore.Cert.SigmaQuarter.Line29
public import CatalanCore.Cert.SigmaQuarter.Line30
public import CatalanCore.Cert.SigmaQuarter.Line31

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo3 : List Macro := Line24Data ++ Line25Data ++ Line26Data ++ Line27Data ++ Line28Data ++ Line29Data ++ Line30Data ++ Line31Data
theorem lineGeo3_shape : (boxes lineGeo3).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo3_cover : IntervalCovers (intervals lineGeo3) (26863 / 32768 : ℚ) (7077 / 8192 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
