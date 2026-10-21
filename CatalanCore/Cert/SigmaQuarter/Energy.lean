module

public import CatalanCore.Cert.SigmaQuarter.EnergyData
public import CatalanCore.Cert.SigmaQuarter.EnergyProof

@[expose] public section

namespace CatalanCore.Cert.SigmaQuarter

theorem I_ok : CatalanLambda.Decay.Irho (1 / 2048 : ℝ) cQ mQ ≤ (90283 / 50000 : ℝ) := by
  apply I_le_of_energy
  rw [energyTot_val]
  norm_num

end CatalanCore.Cert.SigmaQuarter