module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_14 : energyTot (energyChunk 14) = (402033118489300733616483370890362144 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
