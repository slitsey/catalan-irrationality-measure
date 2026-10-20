module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_40 : energyTot (energyChunk 40) = (-82845213145125551391685962881426140426 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
