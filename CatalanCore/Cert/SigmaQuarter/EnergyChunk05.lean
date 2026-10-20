module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_5 : energyTot (energyChunk 5) = (621340918100138484056996110902774552 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
