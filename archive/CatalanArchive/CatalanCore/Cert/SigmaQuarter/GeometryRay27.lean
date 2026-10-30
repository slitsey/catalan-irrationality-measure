module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray216
public import CatalanCore.Cert.SigmaQuarter.Ray217
public import CatalanCore.Cert.SigmaQuarter.Ray218
public import CatalanCore.Cert.SigmaQuarter.Ray219
public import CatalanCore.Cert.SigmaQuarter.Ray220
public import CatalanCore.Cert.SigmaQuarter.Ray221
public import CatalanCore.Cert.SigmaQuarter.Ray222
public import CatalanCore.Cert.SigmaQuarter.Ray223

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo27 : List Macro := Ray216Data ++ Ray217Data ++ Ray218Data ++ Ray219Data ++ Ray220Data ++ Ray221Data ++ Ray222Data ++ Ray223Data
theorem rayGeo27_shape : (boxes rayGeo27).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo27_cover : IntervalCovers (rayIntervals rayGeo27) (12069 / 262144 : ℚ) (6291 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
