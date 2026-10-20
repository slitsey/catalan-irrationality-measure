module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_27 : energyTot (energyChunk 27) = (-219699832506837377949660336731594508 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
