module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray440
public import CatalanCore.Cert.SigmaQuarter.Ray441
public import CatalanCore.Cert.SigmaQuarter.Ray442
public import CatalanCore.Cert.SigmaQuarter.Ray443
public import CatalanCore.Cert.SigmaQuarter.Ray444
public import CatalanCore.Cert.SigmaQuarter.Ray445
public import CatalanCore.Cert.SigmaQuarter.Ray446
public import CatalanCore.Cert.SigmaQuarter.Ray447

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo55 : List Macro := Ray440Data ++ Ray441Data ++ Ray442Data ++ Ray443Data ++ Ray444Data ++ Ray445Data ++ Ray446Data ++ Ray447Data
theorem rayGeo55_shape : (boxes rayGeo55).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo55_cover : IntervalCovers (rayIntervals rayGeo55) (15705 / 131072 : ℚ) (16089 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
