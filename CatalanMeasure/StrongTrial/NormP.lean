module
public import CatalanMeasure.StrongTrial.NormFiniteP
public import CatalanMeasure.StrongTrial.NormLogsP0
public import CatalanMeasure.StrongTrial.NormLogsP1
public import CatalanMeasure.StrongTrial.NormLogsP2
public import CatalanMeasure.StrongTrial.NormLogsP3
public import CatalanMeasure.StrongTrial.NormLogsP4
public import CatalanMeasure.StrongTrial.NormLogsP5
public import CatalanMeasure.StrongTrial.NormLogsP6
public import CatalanMeasure.StrongTrial.NormLogsP7
public import CatalanMeasure.StrongTrial.NormLogsP8
public import CatalanMeasure.StrongTrial.NormLogsP9
public import CatalanMeasure.StrongTrial.NormLogsP10
public import CatalanMeasure.StrongTrial.NormLogsP11
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hLogDecompP : pairTerms P=normChunksP.flatten := by decide +kernel
theorem normP_le : barrierTrialNormSq (trialSeq Pc P) ≤ (NP:ℝ) := by
  apply normSq_le_of_logChunks tailsP finNormP hLogDecompP
  · exact List.Forall₂.cons logChunkP_0 (List.Forall₂.cons logChunkP_1 (List.Forall₂.cons logChunkP_2 (List.Forall₂.cons logChunkP_3 (List.Forall₂.cons logChunkP_4 (List.Forall₂.cons logChunkP_5 (List.Forall₂.cons logChunkP_6 (List.Forall₂.cons logChunkP_7 (List.Forall₂.cons logChunkP_8 (List.Forall₂.cons logChunkP_9 (List.Forall₂.cons logChunkP_10 (List.Forall₂.cons logChunkP_11 (List.Forall₂.cons logChunkP_12 (List.Forall₂.cons logChunkP_13 (List.Forall₂.cons logChunkP_14 (List.Forall₂.cons logChunkP_15 (List.Forall₂.cons logChunkP_16 (List.Forall₂.cons logChunkP_17 (List.Forall₂.cons logChunkP_18 (List.Forall₂.cons logChunkP_19 (List.Forall₂.cons logChunkP_20 (List.Forall₂.cons logChunkP_21 (List.Forall₂.cons logChunkP_22 (List.Forall₂.cons logChunkP_23 (List.Forall₂.cons logChunkP_24 (List.Forall₂.cons logChunkP_25 (List.Forall₂.cons logChunkP_26 (List.Forall₂.cons logChunkP_27 (List.Forall₂.cons logChunkP_28 (List.Forall₂.cons logChunkP_29 (List.Forall₂.cons logChunkP_30 (List.Forall₂.cons logChunkP_31 (List.Forall₂.cons logChunkP_32 (List.Forall₂.cons logChunkP_33 (List.Forall₂.cons logChunkP_34 (List.Forall₂.cons logChunkP_35 (List.Forall₂.cons logChunkP_36 (List.Forall₂.cons logChunkP_37 (List.Forall₂.cons logChunkP_38 (List.Forall₂.cons logChunkP_39 (List.Forall₂.cons logChunkP_40 (List.Forall₂.cons logChunkP_41 (List.Forall₂.cons logChunkP_42 (List.Forall₂.cons logChunkP_43 (List.Forall₂.cons logChunkP_44 (List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))
  · decide +kernel
end CatalanMeasure.StrongTrial
