module
public import CatalanArchive.CatalanMeasure.G728.NormP
public import CatalanArchive.CatalanMeasure.G728.NormV
@[expose] public section
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan
/-- The weighted norm of the two trials is below the cap. -/
theorem weighted_norm_le :
    2 * barrierTrialNormSq (trialSeqS Pc P) + barrierTrialNormSq (trialSeqS Vc V) / 2 ≤
      ((normCap : ℚ) : ℝ) := by
  have h1 := normP_le
  have h2 := normV_le
  have h3 : ((2 * NP + NV / 2 : ℚ) : ℝ) = ((normCap : ℚ) : ℝ) := by rw [normCap_eq]
  push_cast at h3
  linarith
end CatalanMeasure.G728
