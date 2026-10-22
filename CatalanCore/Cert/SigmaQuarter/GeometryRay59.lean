module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray472
public import CatalanCore.Cert.SigmaQuarter.Ray473
public import CatalanCore.Cert.SigmaQuarter.Ray474
public import CatalanCore.Cert.SigmaQuarter.Ray475
public import CatalanCore.Cert.SigmaQuarter.Ray476
public import CatalanCore.Cert.SigmaQuarter.Ray477
public import CatalanCore.Cert.SigmaQuarter.Ray478
public import CatalanCore.Cert.SigmaQuarter.Ray479

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rayGeo59 : List Macro := Ray472Data ++ Ray473Data ++ Ray474Data ++ Ray475Data ++ Ray476Data ++ Ray477Data ++ Ray478Data ++ Ray479Data
theorem rayGeo59_shape : (boxes rayGeo59).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem rayGeo59_cover : IntervalCovers (rayIntervals rayGeo59) (17241 / 131072 : ℚ) (17625 / 131072 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
