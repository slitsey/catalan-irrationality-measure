module
public import CatalanMeasure.StrongTrial.NormFiniteV
public import CatalanMeasure.StrongTrial.NormLogsV0
public import CatalanMeasure.StrongTrial.NormLogsV1
public import CatalanMeasure.StrongTrial.NormLogsV2
public import CatalanMeasure.StrongTrial.NormLogsV3
public import CatalanMeasure.StrongTrial.NormLogsV4
public import CatalanMeasure.StrongTrial.NormLogsV5
public import CatalanMeasure.StrongTrial.NormLogsV6
public import CatalanMeasure.StrongTrial.NormLogsV7
public import CatalanMeasure.StrongTrial.NormLogsV8
public import CatalanMeasure.StrongTrial.NormLogsV9
public import CatalanMeasure.StrongTrial.NormLogsV10
public import CatalanMeasure.StrongTrial.NormLogsV11
public import CatalanMeasure.StrongTrial.NormLogsV12
public import CatalanMeasure.StrongTrial.NormLogsV13
public import CatalanMeasure.StrongTrial.NormLogsV14
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hLogDecompV : pairTerms V=normChunksV.flatten := by decide +kernel
theorem normV_le : barrierTrialNormSq (trialSeq Vc V) ≤ (NV:ℝ) := by
  apply normSq_le_of_logChunks tailsV finNormV hLogDecompV
  · exact List.Forall₂.cons logChunkV_0 (List.Forall₂.cons logChunkV_1 (List.Forall₂.cons logChunkV_2 (List.Forall₂.cons logChunkV_3 (List.Forall₂.cons logChunkV_4 (List.Forall₂.cons logChunkV_5 (List.Forall₂.cons logChunkV_6 (List.Forall₂.cons logChunkV_7 (List.Forall₂.cons logChunkV_8 (List.Forall₂.cons logChunkV_9 (List.Forall₂.cons logChunkV_10 (List.Forall₂.cons logChunkV_11 (List.Forall₂.cons logChunkV_12 (List.Forall₂.cons logChunkV_13 (List.Forall₂.cons logChunkV_14 (List.Forall₂.cons logChunkV_15 (List.Forall₂.cons logChunkV_16 (List.Forall₂.cons logChunkV_17 (List.Forall₂.cons logChunkV_18 (List.Forall₂.cons logChunkV_19 (List.Forall₂.cons logChunkV_20 (List.Forall₂.cons logChunkV_21 (List.Forall₂.cons logChunkV_22 (List.Forall₂.cons logChunkV_23 (List.Forall₂.cons logChunkV_24 (List.Forall₂.cons logChunkV_25 (List.Forall₂.cons logChunkV_26 (List.Forall₂.cons logChunkV_27 (List.Forall₂.cons logChunkV_28 (List.Forall₂.cons logChunkV_29 (List.Forall₂.cons logChunkV_30 (List.Forall₂.cons logChunkV_31 (List.Forall₂.cons logChunkV_32 (List.Forall₂.cons logChunkV_33 (List.Forall₂.cons logChunkV_34 (List.Forall₂.cons logChunkV_35 (List.Forall₂.cons logChunkV_36 (List.Forall₂.cons logChunkV_37 (List.Forall₂.cons logChunkV_38 (List.Forall₂.cons logChunkV_39 (List.Forall₂.cons logChunkV_40 (List.Forall₂.cons logChunkV_41 (List.Forall₂.cons logChunkV_42 (List.Forall₂.cons logChunkV_43 (List.Forall₂.cons logChunkV_44 (List.Forall₂.cons logChunkV_45 (List.Forall₂.cons logChunkV_46 (List.Forall₂.cons logChunkV_47 (List.Forall₂.cons logChunkV_48 (List.Forall₂.cons logChunkV_49 (List.Forall₂.cons logChunkV_50 (List.Forall₂.cons logChunkV_51 (List.Forall₂.cons logChunkV_52 (List.Forall₂.cons logChunkV_53 (List.Forall₂.cons logChunkV_54 (List.Forall₂.cons logChunkV_55 (List.Forall₂.cons logChunkV_56 (List.Forall₂.cons logChunkV_57 (List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · decide +kernel
end CatalanMeasure.StrongTrial
