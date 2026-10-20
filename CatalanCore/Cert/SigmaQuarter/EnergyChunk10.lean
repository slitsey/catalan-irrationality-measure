module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_10 : energyTot (energyChunk 10) = (479616839864675848724253080836328868 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
