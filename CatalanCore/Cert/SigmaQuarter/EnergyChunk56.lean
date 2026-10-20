module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_56 : energyTot (energyChunk 56) = (-37157408384797648211962270425436446813 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
