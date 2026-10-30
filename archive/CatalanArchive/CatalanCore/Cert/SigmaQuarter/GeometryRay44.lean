module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray352
public import CatalanCore.Cert.SigmaQuarter.Ray353
public import CatalanCore.Cert.SigmaQuarter.Ray354
public import CatalanCore.Cert.SigmaQuarter.Ray355
public import CatalanCore.Cert.SigmaQuarter.Ray356
public import CatalanCore.Cert.SigmaQuarter.Ray357
public import CatalanCore.Cert.SigmaQuarter.Ray358
public import CatalanCore.Cert.SigmaQuarter.Ray359

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo44 : List Macro := Ray352Data ++ Ray353Data ++ Ray354Data ++ Ray355Data ++ Ray356Data ++ Ray357Data ++ Ray358Data ++ Ray359Data
theorem rayGeo44_shape : (boxes rayGeo44).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo44_cover : IntervalCovers (rayIntervals rayGeo44) (11481 / 131072 : ℚ) (11865 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
