module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_8 : energyTot (energyChunk 8) = (0 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
