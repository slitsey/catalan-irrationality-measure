module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_35 : energyTot (energyChunk 35) = (-37035602412179211026717993966295900960 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
