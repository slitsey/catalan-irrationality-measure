module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line16
public import CatalanCore.Cert.SigmaQuarter.Line17
public import CatalanCore.Cert.SigmaQuarter.Line18
public import CatalanCore.Cert.SigmaQuarter.Line19
public import CatalanCore.Cert.SigmaQuarter.Line20
public import CatalanCore.Cert.SigmaQuarter.Line21
public import CatalanCore.Cert.SigmaQuarter.Line22
public import CatalanCore.Cert.SigmaQuarter.Line23

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo2 : List Macro := Line16Data ++ Line17Data ++ Line18Data ++ Line19Data ++ Line20Data ++ Line21Data ++ Line22Data ++ Line23Data
theorem lineGeo2_shape : (boxes lineGeo2).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo2_cover : IntervalCovers (intervals lineGeo2) (3587 / 4096 : ℚ) (28811 / 32768 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
