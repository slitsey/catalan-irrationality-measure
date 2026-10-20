module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_9 : energyTot (energyChunk 9) = (500210023567991016626946747863121420 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
