module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_30 : energyTot (energyChunk 30) = (-606676977591427802656285599673060256 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
