module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray232
public import CatalanCore.Cert.SigmaQuarter.Ray233
public import CatalanCore.Cert.SigmaQuarter.Ray234
public import CatalanCore.Cert.SigmaQuarter.Ray235
public import CatalanCore.Cert.SigmaQuarter.Ray236
public import CatalanCore.Cert.SigmaQuarter.Ray237
public import CatalanCore.Cert.SigmaQuarter.Ray238
public import CatalanCore.Cert.SigmaQuarter.Ray239

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo29 : List Macro := Ray232Data ++ Ray233Data ++ Ray234Data ++ Ray235Data ++ Ray236Data ++ Ray237Data ++ Ray238Data ++ Ray239Data
theorem rayGeo29_shape : (boxes rayGeo29).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo29_cover : IntervalCovers (rayIntervals rayGeo29) (26193 / 524288 : ℚ) (27225 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
