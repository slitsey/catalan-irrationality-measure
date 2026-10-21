module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray64
public import CatalanCore.Cert.SigmaQuarter.Ray65
public import CatalanCore.Cert.SigmaQuarter.Ray66
public import CatalanCore.Cert.SigmaQuarter.Ray67
public import CatalanCore.Cert.SigmaQuarter.Ray68
public import CatalanCore.Cert.SigmaQuarter.Ray69
public import CatalanCore.Cert.SigmaQuarter.Ray70
public import CatalanCore.Cert.SigmaQuarter.Ray71

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo8 : List Macro := Ray64Data ++ Ray65Data ++ Ray66Data ++ Ray67Data ++ Ray68Data ++ Ray69Data ++ Ray70Data ++ Ray71Data
theorem rayGeo8_shape : (boxes rayGeo8).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo8_cover : IntervalCovers (rayIntervals rayGeo8) (30663 / 262144 : ℚ) (87 / 512 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
