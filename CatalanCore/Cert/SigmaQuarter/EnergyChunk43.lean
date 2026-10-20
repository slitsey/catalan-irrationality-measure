module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_43 : energyTot (energyChunk 43) = (-81319628410887747369904361158526665224 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
