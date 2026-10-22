module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray376
public import CatalanCore.Cert.SigmaQuarter.Ray377
public import CatalanCore.Cert.SigmaQuarter.Ray378
public import CatalanCore.Cert.SigmaQuarter.Ray379
public import CatalanCore.Cert.SigmaQuarter.Ray380
public import CatalanCore.Cert.SigmaQuarter.Ray381
public import CatalanCore.Cert.SigmaQuarter.Ray382
public import CatalanCore.Cert.SigmaQuarter.Ray383

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo47 : List Macro := Ray376Data ++ Ray377Data ++ Ray378Data ++ Ray379Data ++ Ray380Data ++ Ray381Data ++ Ray382Data ++ Ray383Data
theorem rayGeo47_shape : (boxes rayGeo47).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo47_cover : IntervalCovers (rayIntervals rayGeo47) (12633 / 131072 : ℚ) (13017 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
