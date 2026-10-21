module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray56
public import CatalanCore.Cert.SigmaQuarter.Ray57
public import CatalanCore.Cert.SigmaQuarter.Ray58
public import CatalanCore.Cert.SigmaQuarter.Ray59
public import CatalanCore.Cert.SigmaQuarter.Ray60
public import CatalanCore.Cert.SigmaQuarter.Ray61
public import CatalanCore.Cert.SigmaQuarter.Ray62
public import CatalanCore.Cert.SigmaQuarter.Ray63

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo7 : List Macro := Ray56Data ++ Ray57Data ++ Ray58Data ++ Ray59Data ++ Ray60Data ++ Ray61Data ++ Ray62Data ++ Ray63Data
theorem rayGeo7_shape : (boxes rayGeo7).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo7_cover : IntervalCovers (rayIntervals rayGeo7) (24501 / 262144 : ℚ) (30663 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
