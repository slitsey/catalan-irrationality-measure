module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray136
public import CatalanCore.Cert.SigmaQuarter.Ray137
public import CatalanCore.Cert.SigmaQuarter.Ray138
public import CatalanCore.Cert.SigmaQuarter.Ray139
public import CatalanCore.Cert.SigmaQuarter.Ray140
public import CatalanCore.Cert.SigmaQuarter.Ray141
public import CatalanCore.Cert.SigmaQuarter.Ray142
public import CatalanCore.Cert.SigmaQuarter.Ray143

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo17 : List Macro := Ray136Data ++ Ray137Data ++ Ray138Data ++ Ray139Data ++ Ray140Data ++ Ray141Data ++ Ray142Data ++ Ray143Data
theorem rayGeo17_shape : (boxes rayGeo17).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo17_cover : IntervalCovers (rayIntervals rayGeo17) (29343 / 1048576 : ℚ) (15567 / 524288 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
