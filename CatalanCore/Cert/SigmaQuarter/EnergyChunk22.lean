module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_22 : energyTot (energyChunk 22) = (140758086323451235601837259406829968 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
