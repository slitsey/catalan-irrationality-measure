module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray200
public import CatalanCore.Cert.SigmaQuarter.Ray201
public import CatalanCore.Cert.SigmaQuarter.Ray202
public import CatalanCore.Cert.SigmaQuarter.Ray203
public import CatalanCore.Cert.SigmaQuarter.Ray204
public import CatalanCore.Cert.SigmaQuarter.Ray205
public import CatalanCore.Cert.SigmaQuarter.Ray206
public import CatalanCore.Cert.SigmaQuarter.Ray207

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo25 : List Macro := Ray200Data ++ Ray201Data ++ Ray202Data ++ Ray203Data ++ Ray204Data ++ Ray205Data ++ Ray206Data ++ Ray207Data
theorem rayGeo25_shape : (boxes rayGeo25).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo25_cover : IntervalCovers (rayIntervals rayGeo25) (44319 / 1048576 : ℚ) (23145 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
