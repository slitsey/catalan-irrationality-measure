module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_17 : energyTot (energyChunk 17) = (331018149504227547765339442440619920 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
