module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_58 : energyTot (energyChunk 58) = (-35645150305223725662088711422886290484 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
