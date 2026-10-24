module

public import CatalanMeasure.G728.NormClosed
public import CatalanMeasure.GenD.D58.Cert.NormFinBounds
public import CatalanMeasure.GenD.D58.Cert.NormLogBounds
public import CatalanMeasure.GenD.D58.Cert.Data
public import CatalanMeasure.GenD.D58.Cert.NormFinV0
public import CatalanMeasure.GenD.D58.Cert.NormFinV1
public import CatalanMeasure.GenD.D58.Cert.NormLogV0
public import CatalanMeasure.GenD.D58.Cert.NormLogV1
public import CatalanMeasure.GenD.D58.Cert.NormLogV2
public import CatalanMeasure.GenD.D58.Cert.NormLogV3
public import CatalanMeasure.GenD.D58.Cert.NormLogV4

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def NV : ℚ := 1281392307 / 1000000000
theorem normV_le : barrierTrialNormSq (trialSeqS Vc V) ≤ ((NV : ℚ) : ℝ) := by
  have hf : ∀ g < finUbsV.length, (((V.drop (4 * g)).take 4).map (nCross Vc)).sum ≤ finUbsV.getD g 0 := by
    intro g hg
    have hg' : g < 14 := by simpa [finUbsV] using hg
    interval_cases g
    · exact nfV_0
    · exact nfV_1
    · exact nfV_2
    · exact nfV_3
    · exact nfV_4
    · exact nfV_5
    · exact nfV_6
    · exact nfV_7
    · exact nfV_8
    · exact nfV_9
    · exact nfV_10
    · exact nfV_11
    · exact nfV_12
    · exact nfV_13
  have hl : ∀ g < logBsV.length, logUpperOK (((V.drop (2 * g)).take 2).flatMap (rowTerms V)) (logBsV.getD g 0) = true := by
    intro g hg
    have hg' : g < 28 := by simpa [logBsV] using hg
    interval_cases g
    · exact nlV_0
    · exact nlV_1
    · exact nlV_2
    · exact nlV_3
    · exact nlV_4
    · exact nlV_5
    · exact nlV_6
    · exact nlV_7
    · exact nlV_8
    · exact nlV_9
    · exact nlV_10
    · exact nlV_11
    · exact nlV_12
    · exact nlV_13
    · exact nlV_14
    · exact nlV_15
    · exact nlV_16
    · exact nlV_17
    · exact nlV_18
    · exact nlV_19
    · exact nlV_20
    · exact nlV_21
    · exact nlV_22
    · exact nlV_23
    · exact nlV_24
    · exact nlV_25
    · exact nlV_26
    · exact nlV_27
  refine normSq_le_of_shards tailsV 4 finUbsV sqUbV 2 logBsV ?_ ?_ hf ?_ hl ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
end CatalanMeasure.GenD.D58.Cert
