module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray104
public import CatalanCore.Cert.SigmaQuarter.Ray105
public import CatalanCore.Cert.SigmaQuarter.Ray106
public import CatalanCore.Cert.SigmaQuarter.Ray107
public import CatalanCore.Cert.SigmaQuarter.Ray108
public import CatalanCore.Cert.SigmaQuarter.Ray109
public import CatalanCore.Cert.SigmaQuarter.Ray110
public import CatalanCore.Cert.SigmaQuarter.Ray111

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo13 : List Macro := Ray104Data ++ Ray105Data ++ Ray106Data ++ Ray107Data ++ Ray108Data ++ Ray109Data ++ Ray110Data ++ Ray111Data
theorem rayGeo13_shape : (boxes rayGeo13).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo13_cover : IntervalCovers (rayIntervals rayGeo13) (11109 / 524288 : ℚ) (375 / 16384 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
