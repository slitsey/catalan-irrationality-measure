module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray32
public import CatalanCore.Cert.SigmaQuarter.Ray33
public import CatalanCore.Cert.SigmaQuarter.Ray34
public import CatalanCore.Cert.SigmaQuarter.Ray35
public import CatalanCore.Cert.SigmaQuarter.Ray36
public import CatalanCore.Cert.SigmaQuarter.Ray37
public import CatalanCore.Cert.SigmaQuarter.Ray38
public import CatalanCore.Cert.SigmaQuarter.Ray39

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo4 : List Macro := Ray32Data ++ Ray33Data ++ Ray34Data ++ Ray35Data ++ Ray36Data ++ Ray37Data ++ Ray38Data ++ Ray39Data
theorem rayGeo4_shape : (boxes rayGeo4).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo4_cover : IntervalCovers (rayIntervals rayGeo4) (6933 / 1048576 : ℚ) (2151 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
