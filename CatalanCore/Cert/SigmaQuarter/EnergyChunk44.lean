module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_44 : energyTot (energyChunk 44) = (-73558920732358294203438552756448828396 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
