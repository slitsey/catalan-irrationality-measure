module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray40
public import CatalanCore.Cert.SigmaQuarter.Ray41
public import CatalanCore.Cert.SigmaQuarter.Ray42
public import CatalanCore.Cert.SigmaQuarter.Ray43
public import CatalanCore.Cert.SigmaQuarter.Ray44
public import CatalanCore.Cert.SigmaQuarter.Ray45
public import CatalanCore.Cert.SigmaQuarter.Ray46
public import CatalanCore.Cert.SigmaQuarter.Ray47

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo5 : List Macro := Ray40Data ++ Ray41Data ++ Ray42Data ++ Ray43Data ++ Ray44Data ++ Ray45Data ++ Ray46Data ++ Ray47Data
theorem rayGeo5_shape : (boxes rayGeo5).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo5_cover : IntervalCovers (rayIntervals rayGeo5) (13569 / 262144 : ℚ) (4617 / 65536 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
