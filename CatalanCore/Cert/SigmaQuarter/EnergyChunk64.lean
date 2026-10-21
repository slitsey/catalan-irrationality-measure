module
public import CatalanCore.Cert.SigmaQuarter.EnergyDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem energyChunk_64 : energyTot (energyChunk 64) = (-479301622909026997972166646158695988 : ℤ) := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
