module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_7 : energyTot (energyChunk 7) = (549306412678677734404178153718424538 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
