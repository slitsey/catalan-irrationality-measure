module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_13 : energyTot (energyChunk 13) = (422087848707057558615920108117447456 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
