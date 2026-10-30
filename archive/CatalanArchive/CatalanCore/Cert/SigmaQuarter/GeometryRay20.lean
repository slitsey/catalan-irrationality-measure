module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray160
public import CatalanCore.Cert.SigmaQuarter.Ray161
public import CatalanCore.Cert.SigmaQuarter.Ray162
public import CatalanCore.Cert.SigmaQuarter.Ray163
public import CatalanCore.Cert.SigmaQuarter.Ray164
public import CatalanCore.Cert.SigmaQuarter.Ray165
public import CatalanCore.Cert.SigmaQuarter.Ray166
public import CatalanCore.Cert.SigmaQuarter.Ray167

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo20 : List Macro := Ray160Data ++ Ray161Data ++ Ray162Data ++ Ray163Data ++ Ray164Data ++ Ray165Data ++ Ray166Data ++ Ray167Data
theorem rayGeo20_shape : (boxes rayGeo20).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo20_cover : IntervalCovers (rayIntervals rayGeo20) (34803 / 1048576 : ℚ) (36681 / 1048576 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
