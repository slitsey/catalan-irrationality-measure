module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray424
public import CatalanCore.Cert.SigmaQuarter.Ray425
public import CatalanCore.Cert.SigmaQuarter.Ray426
public import CatalanCore.Cert.SigmaQuarter.Ray427
public import CatalanCore.Cert.SigmaQuarter.Ray428
public import CatalanCore.Cert.SigmaQuarter.Ray429
public import CatalanCore.Cert.SigmaQuarter.Ray430
public import CatalanCore.Cert.SigmaQuarter.Ray431

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo53 : List Macro := Ray424Data ++ Ray425Data ++ Ray426Data ++ Ray427Data ++ Ray428Data ++ Ray429Data ++ Ray430Data ++ Ray431Data
theorem rayGeo53_shape : (boxes rayGeo53).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo53_cover : IntervalCovers (rayIntervals rayGeo53) (14937 / 131072 : ℚ) (15321 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
