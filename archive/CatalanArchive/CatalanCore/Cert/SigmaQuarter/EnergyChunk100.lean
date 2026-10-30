module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_100 : energyTot (energyChunk 100) = (-2359961867578382499811334503401970025 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
