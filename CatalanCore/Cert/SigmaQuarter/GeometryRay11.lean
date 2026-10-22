module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray88
public import CatalanCore.Cert.SigmaQuarter.Ray89
public import CatalanCore.Cert.SigmaQuarter.Ray90
public import CatalanCore.Cert.SigmaQuarter.Ray91
public import CatalanCore.Cert.SigmaQuarter.Ray92
public import CatalanCore.Cert.SigmaQuarter.Ray93
public import CatalanCore.Cert.SigmaQuarter.Ray94
public import CatalanCore.Cert.SigmaQuarter.Ray95

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo11 : List Macro := Ray88Data ++ Ray89Data ++ Ray90Data ++ Ray91Data ++ Ray92Data ++ Ray93Data ++ Ray94Data ++ Ray95Data
theorem rayGeo11_shape : (boxes rayGeo11).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo11_cover : IntervalCovers (rayIntervals rayGeo11) (18759 / 1048576 : ℚ) (5121 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
