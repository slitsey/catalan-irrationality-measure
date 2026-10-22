module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray448
public import CatalanCore.Cert.SigmaQuarter.Ray449
public import CatalanCore.Cert.SigmaQuarter.Ray450
public import CatalanCore.Cert.SigmaQuarter.Ray451
public import CatalanCore.Cert.SigmaQuarter.Ray452
public import CatalanCore.Cert.SigmaQuarter.Ray453
public import CatalanCore.Cert.SigmaQuarter.Ray454
public import CatalanCore.Cert.SigmaQuarter.Ray455

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo56 : List Macro := Ray448Data ++ Ray449Data ++ Ray450Data ++ Ray451Data ++ Ray452Data ++ Ray453Data ++ Ray454Data ++ Ray455Data
theorem rayGeo56_shape : (boxes rayGeo56).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo56_cover : IntervalCovers (rayIntervals rayGeo56) (16089 / 131072 : ℚ) (16473 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
