module

public import CatalanMeasure.G728.NormClosed
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormFinBounds
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogBounds
public import CatalanMeasure.GenD.D58.Cert.Data
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormFinP0
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormFinP1
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogP0
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogP1
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogP2
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogP3
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogP4

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def NP : ℚ := 1661341 / 25000000
theorem normP_le : barrierTrialNormSq (trialSeqS Pc P) ≤ ((NP : ℚ) : ℝ) := by
  have hf : ∀ g < finUbsP.length, (((P.drop (4 * g)).take 4).map (nCross Pc)).sum ≤ finUbsP.getD g 0 := by
    intro g hg
    have hg' : g < 14 := by simpa [finUbsP] using hg
    interval_cases g
    · exact nfP_0
    · exact nfP_1
    · exact nfP_2
    · exact nfP_3
    · exact nfP_4
    · exact nfP_5
    · exact nfP_6
    · exact nfP_7
    · exact nfP_8
    · exact nfP_9
    · exact nfP_10
    · exact nfP_11
    · exact nfP_12
    · exact nfP_13
  have hl : ∀ g < logBsP.length, logUpperOK (((P.drop (2 * g)).take 2).flatMap (rowTerms P)) (logBsP.getD g 0) = true := by
    intro g hg
    have hg' : g < 28 := by simpa [logBsP] using hg
    interval_cases g
    · exact nlP_0
    · exact nlP_1
    · exact nlP_2
    · exact nlP_3
    · exact nlP_4
    · exact nlP_5
    · exact nlP_6
    · exact nlP_7
    · exact nlP_8
    · exact nlP_9
    · exact nlP_10
    · exact nlP_11
    · exact nlP_12
    · exact nlP_13
    · exact nlP_14
    · exact nlP_15
    · exact nlP_16
    · exact nlP_17
    · exact nlP_18
    · exact nlP_19
    · exact nlP_20
    · exact nlP_21
    · exact nlP_22
    · exact nlP_23
    · exact nlP_24
    · exact nlP_25
    · exact nlP_26
    · exact nlP_27
  refine normSq_le_of_shards tailsP 4 finUbsP sqUbP 2 logBsP ?_ ?_ hf ?_ hl ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
end CatalanMeasure.GenD.D58.Cert
