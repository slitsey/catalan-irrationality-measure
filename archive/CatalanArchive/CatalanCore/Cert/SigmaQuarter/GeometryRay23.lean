module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray184
public import CatalanCore.Cert.SigmaQuarter.Ray185
public import CatalanCore.Cert.SigmaQuarter.Ray186
public import CatalanCore.Cert.SigmaQuarter.Ray187
public import CatalanCore.Cert.SigmaQuarter.Ray188
public import CatalanCore.Cert.SigmaQuarter.Ray189
public import CatalanCore.Cert.SigmaQuarter.Ray190
public import CatalanCore.Cert.SigmaQuarter.Ray191

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo23 : List Macro := Ray184Data ++ Ray185Data ++ Ray186Data ++ Ray187Data ++ Ray188Data ++ Ray189Data ++ Ray190Data ++ Ray191Data
theorem rayGeo23_shape : (boxes rayGeo23).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo23_cover : IntervalCovers (rayIntervals rayGeo23) (5055 / 131072 : ℚ) (42369 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
