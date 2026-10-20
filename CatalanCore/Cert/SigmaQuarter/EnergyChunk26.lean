module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_26 : energyTot (energyChunk 26) = (-127704327567087788627215443081652378 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
