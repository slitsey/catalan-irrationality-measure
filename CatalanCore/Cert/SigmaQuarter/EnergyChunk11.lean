module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_11 : energyTot (energyChunk 11) = (460238445144042910708438018159417420 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
