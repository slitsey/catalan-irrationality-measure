module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray208
public import CatalanCore.Cert.SigmaQuarter.Ray209
public import CatalanCore.Cert.SigmaQuarter.Ray210
public import CatalanCore.Cert.SigmaQuarter.Ray211
public import CatalanCore.Cert.SigmaQuarter.Ray212
public import CatalanCore.Cert.SigmaQuarter.Ray213
public import CatalanCore.Cert.SigmaQuarter.Ray214
public import CatalanCore.Cert.SigmaQuarter.Ray215

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo26 : List Macro := Ray208Data ++ Ray209Data ++ Ray210Data ++ Ray211Data ++ Ray212Data ++ Ray213Data ++ Ray214Data ++ Ray215Data
theorem rayGeo26_shape : (boxes rayGeo26).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo26_cover : IntervalCovers (rayIntervals rayGeo26) (23145 / 524288 : ℚ) (12069 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
