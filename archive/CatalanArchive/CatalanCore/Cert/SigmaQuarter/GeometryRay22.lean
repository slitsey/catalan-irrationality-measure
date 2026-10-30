module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray176
public import CatalanCore.Cert.SigmaQuarter.Ray177
public import CatalanCore.Cert.SigmaQuarter.Ray178
public import CatalanCore.Cert.SigmaQuarter.Ray179
public import CatalanCore.Cert.SigmaQuarter.Ray180
public import CatalanCore.Cert.SigmaQuarter.Ray181
public import CatalanCore.Cert.SigmaQuarter.Ray182
public import CatalanCore.Cert.SigmaQuarter.Ray183

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo22 : List Macro := Ray176Data ++ Ray177Data ++ Ray178Data ++ Ray179Data ++ Ray180Data ++ Ray181Data ++ Ray182Data ++ Ray183Data
theorem rayGeo22_shape : (boxes rayGeo22).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo22_cover : IntervalCovers (rayIntervals rayGeo22) (9645 / 262144 : ℚ) (5055 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
