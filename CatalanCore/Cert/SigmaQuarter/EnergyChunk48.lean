module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_48 : energyTot (energyChunk 48) = (-17978059268918108964122836552301881506 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
