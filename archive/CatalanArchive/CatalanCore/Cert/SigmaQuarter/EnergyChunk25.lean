module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_25 : energyTot (energyChunk 25) = (0 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
