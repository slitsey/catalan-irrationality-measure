module
public import CatalanMeasure.FirstStrongTrial.NormP
public import CatalanMeasure.FirstStrongTrial.NormV
public import CatalanMeasure.Parametric.StrongBudgets
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
noncomputable section

def physicalP (j : ℕ) : ℝ := 2*trialSeq Pc P j
def physicalV : ℕ → ℝ := trialSeq Vc V

theorem normP_le : barrierTrialNormSq (trialSeq Pc P) ≤ (NP:ℝ) := normOK_spec hNP
theorem normV_le : barrierTrialNormSq (trialSeq Vc V) ≤ (NV:ℝ) := normOK_spec hNV

theorem physical_norm_le : barrierTrialNormSq physicalP+barrierTrialNormSq physicalV/2 ≤
    Parametric.strongNormFirst := by
  have hp := normP_le
  have hv := normV_le
  unfold physicalP physicalV
  rw [population_trialNormSq_mul]
  norm_num [NP,NV,Parametric.strongNormFirst] at hp hv ⊢
  linarith only [hp,hv]

end
end CatalanMeasure.FirstStrongTrial
