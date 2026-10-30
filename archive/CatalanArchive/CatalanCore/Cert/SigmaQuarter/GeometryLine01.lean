module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line8
public import CatalanCore.Cert.SigmaQuarter.Line9
public import CatalanCore.Cert.SigmaQuarter.Line10
public import CatalanCore.Cert.SigmaQuarter.Line11
public import CatalanCore.Cert.SigmaQuarter.Line12
public import CatalanCore.Cert.SigmaQuarter.Line13
public import CatalanCore.Cert.SigmaQuarter.Line14
public import CatalanCore.Cert.SigmaQuarter.Line15

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo1 : List Macro := Line8Data ++ Line9Data ++ Line10Data ++ Line11Data ++ Line12Data ++ Line13Data ++ Line14Data ++ Line15Data
theorem lineGeo1_shape : (boxes lineGeo1).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo1_cover : IntervalCovers (intervals lineGeo1) (12195 / 16384 : ℚ) (25723 / 32768 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
