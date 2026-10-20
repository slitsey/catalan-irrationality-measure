module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_49 : energyTot (energyChunk 49) = (-6899379976492634432478711130927397110 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
