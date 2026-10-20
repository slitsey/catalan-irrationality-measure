module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_0 : energyTot (energyChunk 0) = (2251696240432633873780403351025198378 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
