module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_20 : energyTot (energyChunk 20) = (231485568560275572237438827292156128 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
