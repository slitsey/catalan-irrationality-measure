module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_128 : energyTot (energyChunk 128) = (-3478211661319950065813576977854357689 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
