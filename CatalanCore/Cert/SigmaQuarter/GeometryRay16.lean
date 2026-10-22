module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray128
public import CatalanCore.Cert.SigmaQuarter.Ray129
public import CatalanCore.Cert.SigmaQuarter.Ray130
public import CatalanCore.Cert.SigmaQuarter.Ray131
public import CatalanCore.Cert.SigmaQuarter.Ray132
public import CatalanCore.Cert.SigmaQuarter.Ray133
public import CatalanCore.Cert.SigmaQuarter.Ray134
public import CatalanCore.Cert.SigmaQuarter.Ray135

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo16 : List Macro := Ray128Data ++ Ray129Data ++ Ray130Data ++ Ray131Data ++ Ray132Data ++ Ray133Data ++ Ray134Data ++ Ray135Data
theorem rayGeo16_shape : (boxes rayGeo16).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo16_cover : IntervalCovers (rayIntervals rayGeo16) (13761 / 524288 : ℚ) (29343 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
