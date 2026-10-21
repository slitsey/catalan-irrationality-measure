module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_32 : energyTot (energyChunk 32) = (224874067108623474201877942944516436 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
