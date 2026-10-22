module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray480
public import CatalanCore.Cert.SigmaQuarter.Ray481
public import CatalanCore.Cert.SigmaQuarter.Ray482
public import CatalanCore.Cert.SigmaQuarter.Ray483
public import CatalanCore.Cert.SigmaQuarter.Ray484
public import CatalanCore.Cert.SigmaQuarter.Ray485
public import CatalanCore.Cert.SigmaQuarter.Ray486
public import CatalanCore.Cert.SigmaQuarter.Ray487

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo60 : List Macro := Ray480Data ++ Ray481Data ++ Ray482Data ++ Ray483Data ++ Ray484Data ++ Ray485Data ++ Ray486Data ++ Ray487Data
theorem rayGeo60_shape : (boxes rayGeo60).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo60_cover : IntervalCovers (rayIntervals rayGeo60) (17625 / 131072 : ℚ) (18009 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
