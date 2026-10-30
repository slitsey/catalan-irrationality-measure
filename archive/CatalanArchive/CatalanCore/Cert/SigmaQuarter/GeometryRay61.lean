module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray488
public import CatalanCore.Cert.SigmaQuarter.Ray489
public import CatalanCore.Cert.SigmaQuarter.Ray490
public import CatalanCore.Cert.SigmaQuarter.Ray491
public import CatalanCore.Cert.SigmaQuarter.Ray492
public import CatalanCore.Cert.SigmaQuarter.Ray493
public import CatalanCore.Cert.SigmaQuarter.Ray494
public import CatalanCore.Cert.SigmaQuarter.Ray495

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo61 : List Macro := Ray488Data ++ Ray489Data ++ Ray490Data ++ Ray491Data ++ Ray492Data ++ Ray493Data ++ Ray494Data ++ Ray495Data
theorem rayGeo61_shape : (boxes rayGeo61).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo61_cover : IntervalCovers (rayIntervals rayGeo61) (18009 / 131072 : ℚ) (579 / 512 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
