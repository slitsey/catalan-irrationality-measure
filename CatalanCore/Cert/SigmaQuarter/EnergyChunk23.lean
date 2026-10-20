module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_23 : energyTot (energyChunk 23) = (85897558924928329928480504683057422 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
