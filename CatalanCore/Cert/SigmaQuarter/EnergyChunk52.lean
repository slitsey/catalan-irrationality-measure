module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_52 : energyTot (energyChunk 52) = (-39045723389113978147060476339396331131 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
