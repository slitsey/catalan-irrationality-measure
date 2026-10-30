module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray400
public import CatalanCore.Cert.SigmaQuarter.Ray401
public import CatalanCore.Cert.SigmaQuarter.Ray402
public import CatalanCore.Cert.SigmaQuarter.Ray403
public import CatalanCore.Cert.SigmaQuarter.Ray404
public import CatalanCore.Cert.SigmaQuarter.Ray405
public import CatalanCore.Cert.SigmaQuarter.Ray406
public import CatalanCore.Cert.SigmaQuarter.Ray407

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo50 : List Macro := Ray400Data ++ Ray401Data ++ Ray402Data ++ Ray403Data ++ Ray404Data ++ Ray405Data ++ Ray406Data ++ Ray407Data
theorem rayGeo50_shape : (boxes rayGeo50).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo50_cover : IntervalCovers (rayIntervals rayGeo50) (13785 / 131072 : ℚ) (14169 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
