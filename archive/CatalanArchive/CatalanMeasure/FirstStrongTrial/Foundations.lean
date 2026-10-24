module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.AQ
public import CatalanMeasure.FirstStrongTrial.First
public import CatalanMeasure.Cert.ExplicitIntegerGap
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000

theorem hIntX : AX=lpSmul scaleX (AZX.map (fun z : ℤ => (z:ℚ))) := by decide +kernel
theorem hIntY : AY=lpSmul scaleY (AZY.map (fun z : ℤ => (z:ℚ))) := by decide +kernel
theorem hScaleX : scaleX≠0 := by decide +kernel
theorem hScaleY : scaleY≠0 := by decide +kernel
theorem hchainX : rowCheck P V AX planX=true := by decide +kernel
theorem hchainY : colCheck V AY planY=true := by decide +kernel
theorem hendX : shiftedRowEndOK R Pc Vc P V MX=true := by decide +kernel

end CatalanMeasure.FirstStrongTrial
