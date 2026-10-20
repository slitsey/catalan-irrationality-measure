module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_31 : energyTot (energyChunk 31) = (-822910679858081166083222660037678162 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
