module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_12 : energyTot (energyChunk 12) = (441287088083811375177303112692164488 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
