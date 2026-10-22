module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray408
public import CatalanCore.Cert.SigmaQuarter.Ray409
public import CatalanCore.Cert.SigmaQuarter.Ray410
public import CatalanCore.Cert.SigmaQuarter.Ray411
public import CatalanCore.Cert.SigmaQuarter.Ray412
public import CatalanCore.Cert.SigmaQuarter.Ray413
public import CatalanCore.Cert.SigmaQuarter.Ray414
public import CatalanCore.Cert.SigmaQuarter.Ray415

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo51 : List Macro := Ray408Data ++ Ray409Data ++ Ray410Data ++ Ray411Data ++ Ray412Data ++ Ray413Data ++ Ray414Data ++ Ray415Data
theorem rayGeo51_shape : (boxes rayGeo51).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo51_cover : IntervalCovers (rayIntervals rayGeo51) (14169 / 131072 : ℚ) (14553 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
