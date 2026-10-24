module
public import CatalanMeasure.FirstStrongTrial.NormP
public import CatalanMeasure.FirstStrongTrial.NormV
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
noncomputable section

def physicalP (j : ℕ) : ℝ := 2*trialSeq Pc P j
def physicalV : ℕ → ℝ := trialSeq Vc V

theorem normP_le : barrierTrialNormSq (trialSeq Pc P) ≤ (NP:ℝ) := normOK_spec hNP
theorem normV_le : barrierTrialNormSq (trialSeq Vc V) ≤ (NV:ℝ) := normOK_spec hNV

end
end CatalanMeasure.FirstStrongTrial
