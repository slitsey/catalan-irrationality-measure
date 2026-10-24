module
public import CatalanArchive.CatalanMeasure.StrongTrial.AQ
public import CatalanArchive.CatalanMeasure.StrongTrial.ResidualAQ
public import CatalanArchive.CatalanMeasure.StrongTrial.First
public import CatalanMeasure.Cert.ExplicitIntegerGap
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000

theorem hIntX : AX=lpSmul scaleX (AZX.map (fun z : ℤ => (z:ℚ))) := by decide +kernel
theorem hIntY : AY=lpSmul scaleY (AZY.map (fun z : ℤ => (z:ℚ))) := by decide +kernel
theorem hIntR : AR=lpSmul scaleR (AZR.map (fun z : ℤ => (z:ℚ))) := by decide +kernel
theorem hScaleX : scaleX≠0 := by decide +kernel
theorem hScaleY : scaleY≠0 := by decide +kernel
theorem hScaleR : scaleR≠0 := by decide +kernel
theorem hchainX : rowCheck P V AX planX=true := by decide +kernel
theorem hchainY : colCheck V AY planY=true := by decide +kernel
theorem hendX : shiftedRowEndOK R Pc Vc P V MX=true := by decide +kernel
theorem hcoverR0 : coverFrom AR [] (-1) planR0 0=true := by decide +kernel
theorem hcoverR1 : coverFrom AR [] 0 planR1 1=true := by decide +kernel
theorem hendRLeft : markedResidualEndOK Pc P MR (-1)=true := by decide +kernel
theorem hendRMid : markedResidualEndOK Pc P MR 0=true := by decide +kernel
theorem hendRRight : markedResidualEndOK Pc P MR 1=true := by decide +kernel

end CatalanMeasure.StrongTrial
