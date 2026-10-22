module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray168
public import CatalanCore.Cert.SigmaQuarter.Ray169
public import CatalanCore.Cert.SigmaQuarter.Ray170
public import CatalanCore.Cert.SigmaQuarter.Ray171
public import CatalanCore.Cert.SigmaQuarter.Ray172
public import CatalanCore.Cert.SigmaQuarter.Ray173
public import CatalanCore.Cert.SigmaQuarter.Ray174
public import CatalanCore.Cert.SigmaQuarter.Ray175

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo21 : List Macro := Ray168Data ++ Ray169Data ++ Ray170Data ++ Ray171Data ++ Ray172Data ++ Ray173Data ++ Ray174Data ++ Ray175Data
theorem rayGeo21_shape : (boxes rayGeo21).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo21_cover : IntervalCovers (rayIntervals rayGeo21) (36681 / 1048576 : ℚ) (9645 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
