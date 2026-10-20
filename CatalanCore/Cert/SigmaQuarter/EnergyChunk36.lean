module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_36 : energyTot (energyChunk 36) = (-49132159680845531773573645710262180270 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
