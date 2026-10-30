module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray464
public import CatalanCore.Cert.SigmaQuarter.Ray465
public import CatalanCore.Cert.SigmaQuarter.Ray466
public import CatalanCore.Cert.SigmaQuarter.Ray467
public import CatalanCore.Cert.SigmaQuarter.Ray468
public import CatalanCore.Cert.SigmaQuarter.Ray469
public import CatalanCore.Cert.SigmaQuarter.Ray470
public import CatalanCore.Cert.SigmaQuarter.Ray471

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo58 : List Macro := Ray464Data ++ Ray465Data ++ Ray466Data ++ Ray467Data ++ Ray468Data ++ Ray469Data ++ Ray470Data ++ Ray471Data
theorem rayGeo58_shape : (boxes rayGeo58).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo58_cover : IntervalCovers (rayIntervals rayGeo58) (16857 / 131072 : ℚ) (17241 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
