module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_28 : energyTot (energyChunk 28) = (-325876003255565335785470199696924264 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
