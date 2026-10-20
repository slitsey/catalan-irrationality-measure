module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_2 : energyTot (energyChunk 2) = (879903105865014958416812233851592568 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
