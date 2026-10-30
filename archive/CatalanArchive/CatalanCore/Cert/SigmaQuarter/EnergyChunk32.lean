module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_32 : energyTot (energyChunk 32) = (-239218375422068886601576816260539930 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
