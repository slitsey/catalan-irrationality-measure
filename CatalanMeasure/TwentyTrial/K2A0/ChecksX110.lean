module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX110 : integerGapOK AZX ((1168499 / 2000000 : ℚ),(2921249 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX110 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1168499 / 2000000 : ℚ),(2921249 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
