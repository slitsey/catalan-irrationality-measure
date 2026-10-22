module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray80
public import CatalanCore.Cert.SigmaQuarter.Ray81
public import CatalanCore.Cert.SigmaQuarter.Ray82
public import CatalanCore.Cert.SigmaQuarter.Ray83
public import CatalanCore.Cert.SigmaQuarter.Ray84
public import CatalanCore.Cert.SigmaQuarter.Ray85
public import CatalanCore.Cert.SigmaQuarter.Ray86
public import CatalanCore.Cert.SigmaQuarter.Ray87

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo10 : List Macro := Ray80Data ++ Ray81Data ++ Ray82Data ++ Ray83Data ++ Ray84Data ++ Ray85Data ++ Ray86Data ++ Ray87Data
theorem rayGeo10_shape : (boxes rayGeo10).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo10_cover : IntervalCovers (rayIntervals rayGeo10) (8523 / 524288 : ℚ) (18759 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
