module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray152
public import CatalanCore.Cert.SigmaQuarter.Ray153
public import CatalanCore.Cert.SigmaQuarter.Ray154
public import CatalanCore.Cert.SigmaQuarter.Ray155
public import CatalanCore.Cert.SigmaQuarter.Ray156
public import CatalanCore.Cert.SigmaQuarter.Ray157
public import CatalanCore.Cert.SigmaQuarter.Ray158
public import CatalanCore.Cert.SigmaQuarter.Ray159

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo19 : List Macro := Ray152Data ++ Ray153Data ++ Ray154Data ++ Ray155Data ++ Ray156Data ++ Ray157Data ++ Ray158Data ++ Ray159Data
theorem rayGeo19_shape : (boxes rayGeo19).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo19_cover : IntervalCovers (rayIntervals rayGeo19) (32985 / 1048576 : ℚ) (34803 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
