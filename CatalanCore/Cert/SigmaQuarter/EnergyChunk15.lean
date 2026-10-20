module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_15 : energyTot (energyChunk 15) = (380547050872759307151610470518178566 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
