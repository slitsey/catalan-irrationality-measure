module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_51 : energyTot (energyChunk 51) = (-39085639056226373340102020840283602870 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
