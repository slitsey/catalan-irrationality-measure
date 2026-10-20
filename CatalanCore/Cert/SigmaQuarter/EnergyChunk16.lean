module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_16 : energyTot (energyChunk 16) = (357065517043656238494594817888378370 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
