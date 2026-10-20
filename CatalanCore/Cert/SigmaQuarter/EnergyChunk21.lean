module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energyChunk_21 : energyTot (energyChunk 21) = (189027628910160115206237778490156994 : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaQuarter
