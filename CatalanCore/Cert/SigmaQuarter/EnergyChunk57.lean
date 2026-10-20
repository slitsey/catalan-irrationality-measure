module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_57 : energyTot (energyChunk 57) = (-36425390292645466258585783108614840170 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
