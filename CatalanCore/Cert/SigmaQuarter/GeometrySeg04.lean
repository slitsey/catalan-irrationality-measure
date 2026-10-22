module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg32
public import CatalanCore.Cert.SigmaQuarter.Seg33
public import CatalanCore.Cert.SigmaQuarter.Seg34
public import CatalanCore.Cert.SigmaQuarter.Seg35
public import CatalanCore.Cert.SigmaQuarter.Seg36
public import CatalanCore.Cert.SigmaQuarter.Seg37
public import CatalanCore.Cert.SigmaQuarter.Seg38
public import CatalanCore.Cert.SigmaQuarter.Seg39

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segGeo4 : List Macro := Seg32Data ++ Seg33Data ++ Seg34Data ++ Seg35Data ++ Seg36Data ++ Seg37Data ++ Seg38Data ++ Seg39Data
theorem segGeo4_shape : (boxes segGeo4).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem segGeo4_cover : IntervalCovers (intervals segGeo4) (-69793218561 / 1099511627776 : ℚ) (-29742648525 / 549755813888 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
theorem segGeo4_cost : ((boxes segGeo4).map segCost).sum = (-20956840339359933439227 / 14757395258967641292800000 : ℚ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
