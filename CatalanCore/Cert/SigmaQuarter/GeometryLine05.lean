module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line40
public import CatalanCore.Cert.SigmaQuarter.Line41
public import CatalanCore.Cert.SigmaQuarter.Line42
public import CatalanCore.Cert.SigmaQuarter.Line43
public import CatalanCore.Cert.SigmaQuarter.Line44
public import CatalanCore.Cert.SigmaQuarter.Line45
public import CatalanCore.Cert.SigmaQuarter.Line46
public import CatalanCore.Cert.SigmaQuarter.Line47

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo5 : List Macro := Line40Data ++ Line41Data ++ Line42Data ++ Line43Data ++ Line44Data ++ Line45Data ++ Line46Data ++ Line47Data
theorem lineGeo5_shape : (boxes lineGeo5).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo5_cover : IntervalCovers (intervals lineGeo5) (3687 / 4096 : ℚ) (15161 / 16384 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
