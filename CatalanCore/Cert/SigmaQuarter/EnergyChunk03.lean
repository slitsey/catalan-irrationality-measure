module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_3 : energyTot (energyChunk 3) = (753515941624344208690205858749984986 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
