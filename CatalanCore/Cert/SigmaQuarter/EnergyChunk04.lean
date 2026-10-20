module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_4 : energyTot (energyChunk 4) = (675434410899182572689568532590455314 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
