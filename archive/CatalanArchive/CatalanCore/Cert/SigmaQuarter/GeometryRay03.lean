module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray24
public import CatalanCore.Cert.SigmaQuarter.Ray25
public import CatalanCore.Cert.SigmaQuarter.Ray26
public import CatalanCore.Cert.SigmaQuarter.Ray27
public import CatalanCore.Cert.SigmaQuarter.Ray28
public import CatalanCore.Cert.SigmaQuarter.Ray29
public import CatalanCore.Cert.SigmaQuarter.Ray30
public import CatalanCore.Cert.SigmaQuarter.Ray31

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo3 : List Macro := Ray24Data ++ Ray25Data ++ Ray26Data ++ Ray27Data ++ Ray28Data ++ Ray29Data ++ Ray30Data ++ Ray31Data
theorem rayGeo3_shape : (boxes rayGeo3).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo3_cover : IntervalCovers (rayIntervals rayGeo3) (5271 / 1048576 : ℚ) (6933 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
