module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_53 : energyTot (energyChunk 53) = (-38761604092718585742801094250726672242 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
