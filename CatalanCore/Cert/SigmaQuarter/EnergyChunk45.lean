module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_45 : energyTot (energyChunk 45) = (-62298261698090929423949007865505838866 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
