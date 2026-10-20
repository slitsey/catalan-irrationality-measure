module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_33 : energyTot (energyChunk 33) = (-5416864167487412054972455064320421812 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
