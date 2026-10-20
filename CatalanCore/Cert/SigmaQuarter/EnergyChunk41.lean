module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_41 : energyTot (energyChunk 41) = (-85689278531432868756858731228461364170 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
