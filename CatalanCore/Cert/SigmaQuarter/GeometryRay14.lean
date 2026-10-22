module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray112
public import CatalanCore.Cert.SigmaQuarter.Ray113
public import CatalanCore.Cert.SigmaQuarter.Ray114
public import CatalanCore.Cert.SigmaQuarter.Ray115
public import CatalanCore.Cert.SigmaQuarter.Ray116
public import CatalanCore.Cert.SigmaQuarter.Ray117
public import CatalanCore.Cert.SigmaQuarter.Ray118
public import CatalanCore.Cert.SigmaQuarter.Ray119

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo14 : List Macro := Ray112Data ++ Ray113Data ++ Ray114Data ++ Ray115Data ++ Ray116Data ++ Ray117Data ++ Ray118Data ++ Ray119Data
theorem rayGeo14_shape : (boxes rayGeo14).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo14_cover : IntervalCovers (rayIntervals rayGeo14) (375 / 16384 : ℚ) (12879 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
