module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX45 : integerGapOK AZX ((-69809 / 100000 : ℚ),(-6980897 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX45 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-69809 / 100000 : ℚ),(-6980897 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
