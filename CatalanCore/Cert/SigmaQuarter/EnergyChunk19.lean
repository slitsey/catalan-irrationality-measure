module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_19 : energyTot (energyChunk 19) = (268856007004723853501456519959106198 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
