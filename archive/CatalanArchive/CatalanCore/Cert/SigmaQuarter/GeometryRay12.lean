module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray96
public import CatalanCore.Cert.SigmaQuarter.Ray97
public import CatalanCore.Cert.SigmaQuarter.Ray98
public import CatalanCore.Cert.SigmaQuarter.Ray99
public import CatalanCore.Cert.SigmaQuarter.Ray100
public import CatalanCore.Cert.SigmaQuarter.Ray101
public import CatalanCore.Cert.SigmaQuarter.Ray102
public import CatalanCore.Cert.SigmaQuarter.Ray103

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo12 : List Macro := Ray96Data ++ Ray97Data ++ Ray98Data ++ Ray99Data ++ Ray100Data ++ Ray101Data ++ Ray102Data ++ Ray103Data
theorem rayGeo12_shape : (boxes rayGeo12).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo12_cover : IntervalCovers (rayIntervals rayGeo12) (5121 / 262144 : ℚ) (11109 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
