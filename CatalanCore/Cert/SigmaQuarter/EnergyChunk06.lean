module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_6 : energyTot (energyChunk 6) = (581062096040556633207296049225425166 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
