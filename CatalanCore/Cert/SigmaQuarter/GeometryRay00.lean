module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray0
public import CatalanCore.Cert.SigmaQuarter.Ray1
public import CatalanCore.Cert.SigmaQuarter.Ray2
public import CatalanCore.Cert.SigmaQuarter.Ray3
public import CatalanCore.Cert.SigmaQuarter.Ray4
public import CatalanCore.Cert.SigmaQuarter.Ray5
public import CatalanCore.Cert.SigmaQuarter.Ray6
public import CatalanCore.Cert.SigmaQuarter.Ray7

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo0 : List Macro := Ray0Data ++ Ray1Data ++ Ray2Data ++ Ray3Data ++ Ray4Data ++ Ray5Data ++ Ray6Data ++ Ray7Data
theorem rayGeo0_shape : (boxes rayGeo0).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo0_cover : IntervalCovers (rayIntervals rayGeo0) (0 / 1 : ℚ) (1227 / 262144 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
