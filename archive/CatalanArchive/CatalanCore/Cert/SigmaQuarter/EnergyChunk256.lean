module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_256 : energyTot (energyChunk 256) = (-9369001491931976013988262544237583498 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
