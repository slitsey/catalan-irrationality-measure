module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_50 : energyTot (energyChunk 50) = (-22679352653355334228508589647434902813 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
