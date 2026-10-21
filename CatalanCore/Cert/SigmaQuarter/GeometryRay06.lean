module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray48
public import CatalanCore.Cert.SigmaQuarter.Ray49
public import CatalanCore.Cert.SigmaQuarter.Ray50
public import CatalanCore.Cert.SigmaQuarter.Ray51
public import CatalanCore.Cert.SigmaQuarter.Ray52
public import CatalanCore.Cert.SigmaQuarter.Ray53
public import CatalanCore.Cert.SigmaQuarter.Ray54
public import CatalanCore.Cert.SigmaQuarter.Ray55

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo6 : List Macro := Ray48Data ++ Ray49Data ++ Ray50Data ++ Ray51Data ++ Ray52Data ++ Ray53Data ++ Ray54Data ++ Ray55Data
theorem rayGeo6_shape : (boxes rayGeo6).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo6_cover : IntervalCovers (rayIntervals rayGeo6) (4617 / 65536 : ℚ) (24501 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
