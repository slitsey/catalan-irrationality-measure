module
public import CatalanArchive.CatalanMeasure.StrongTrial.NormP
public import CatalanArchive.CatalanMeasure.StrongTrial.NormV
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan

theorem weighted_norm_le :
    2*barrierTrialNormSq (trialSeq Pc P)+barrierTrialNormSq (trialSeq Vc V)/2 ≤
      (77424975/100000000:ℝ) := by
  have hp := normP_le
  have hv := normV_le
  norm_num [NP,NV] at hp hv
  linarith only [hp,hv]

end CatalanMeasure.StrongTrial
