module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_18 : energyTot (energyChunk 18) = (301819117594492493922603823596530892 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
