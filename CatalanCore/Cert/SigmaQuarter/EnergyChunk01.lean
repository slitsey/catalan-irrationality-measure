module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_1 : energyTot (energyChunk 1) = (1136733226369742496945868506166103634 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
