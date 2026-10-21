module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line0
public import CatalanCore.Cert.SigmaQuarter.Line1
public import CatalanCore.Cert.SigmaQuarter.Line2
public import CatalanCore.Cert.SigmaQuarter.Line3
public import CatalanCore.Cert.SigmaQuarter.Line4
public import CatalanCore.Cert.SigmaQuarter.Line5
public import CatalanCore.Cert.SigmaQuarter.Line6
public import CatalanCore.Cert.SigmaQuarter.Line7

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo0 : List Macro := Line0Data ++ Line1Data ++ Line2Data ++ Line3Data ++ Line4Data ++ Line5Data ++ Line6Data ++ Line7Data
theorem lineGeo0_shape : (boxes lineGeo0).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo0_cover : IntervalCovers (intervals lineGeo0) (0 / 1 : ℚ) (1775 / 2048 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
