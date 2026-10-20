module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_32 : energyTot (energyChunk 32) = (-1224593584974951341841306606934136466 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
