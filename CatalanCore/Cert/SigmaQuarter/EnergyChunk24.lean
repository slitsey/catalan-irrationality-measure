module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_24 : energyTot (energyChunk 24) = (23582813837772719226081671368648476 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
