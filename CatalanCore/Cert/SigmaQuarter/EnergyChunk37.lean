module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_37 : energyTot (energyChunk 37) = (-60043932091318261405414016863870135792 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
