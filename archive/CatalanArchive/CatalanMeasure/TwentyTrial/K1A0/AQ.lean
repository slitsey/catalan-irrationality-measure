module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem hAQX : fracSum (shiftedRowFracs R Pc Vc P V)=(AX,QX) :=by decide +kernel
theorem hAQY : fracSum (shiftedColumnFracs C Vc V)=(AY,QY) :=by decide +kernel
theorem hIntX : AX=lpSmul scaleX (AZX.map (fun z:ℤ =>(z:ℚ))) :=by decide +kernel
theorem hIntY : AY=lpSmul scaleY (AZY.map (fun z:ℤ =>(z:ℚ))) :=by decide +kernel
theorem hScaleX : scaleX≠0 :=by decide +kernel
theorem hScaleY : scaleY≠0 :=by decide +kernel
theorem hchainX : rowCheck P V AX planX=true :=by decide +kernel
theorem hchainY : colCheck V AY planY=true :=by decide +kernel
theorem hendX : shiftedRowEndOK R Pc Vc P V MX=true :=by decide +kernel
theorem hNP : normOK Pc P NP=true :=by decide +kernel
theorem hNV : normOK Vc V NV=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
