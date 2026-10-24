module
public import CatalanArchive.CatalanMeasure.StrongTrial.Data
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem tailsP : tailsInDisk P = true := by decide +kernel
theorem tailsV : tailsInDisk V = true := by decide +kernel
theorem first_lower : (9/50:ℝ) ≤ trialSeq Pc P 1 := by
  norm_num [trialSeq,barrierTrial,barrierFiniteCoeff,Pc,P,TailQ.toC,barrierComplex,Complex.mul_re]
end CatalanMeasure.StrongTrial
