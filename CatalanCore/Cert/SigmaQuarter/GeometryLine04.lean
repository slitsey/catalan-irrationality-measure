module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line32
public import CatalanCore.Cert.SigmaQuarter.Line33
public import CatalanCore.Cert.SigmaQuarter.Line34
public import CatalanCore.Cert.SigmaQuarter.Line35
public import CatalanCore.Cert.SigmaQuarter.Line36
public import CatalanCore.Cert.SigmaQuarter.Line37
public import CatalanCore.Cert.SigmaQuarter.Line38
public import CatalanCore.Cert.SigmaQuarter.Line39

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lineGeo4 : List Macro := Line32Data ++ Line33Data ++ Line34Data ++ Line35Data ++ Line36Data ++ Line37Data ++ Line38Data ++ Line39Data
theorem lineGeo4_shape : (boxes lineGeo4).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem lineGeo4_cover : IntervalCovers (intervals lineGeo4) (28875 / 32768 : ℚ) (28939 / 32768 : ℚ) :=
  chainCovers_sound _ _ _ (by decide +kernel)
end CatalanCore.Cert.SigmaQuarter
