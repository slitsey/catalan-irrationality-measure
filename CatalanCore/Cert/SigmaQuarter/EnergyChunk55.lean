module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_55 : energyTot (energyChunk 55) = (-37797123377592777338938292611896577126 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
