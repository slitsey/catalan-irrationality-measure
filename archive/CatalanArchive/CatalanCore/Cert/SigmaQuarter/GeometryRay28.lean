module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray224
public import CatalanCore.Cert.SigmaQuarter.Ray225
public import CatalanCore.Cert.SigmaQuarter.Ray226
public import CatalanCore.Cert.SigmaQuarter.Ray227
public import CatalanCore.Cert.SigmaQuarter.Ray228
public import CatalanCore.Cert.SigmaQuarter.Ray229
public import CatalanCore.Cert.SigmaQuarter.Ray230
public import CatalanCore.Cert.SigmaQuarter.Ray231

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo28 : List Macro := Ray224Data ++ Ray225Data ++ Ray226Data ++ Ray227Data ++ Ray228Data ++ Ray229Data ++ Ray230Data ++ Ray231Data
theorem rayGeo28_shape : (boxes rayGeo28).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo28_cover : IntervalCovers (rayIntervals rayGeo28) (6291 / 131072 : ℚ) (26193 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
