module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX98 : integerGapOK AZX ((3676077 / 10000000 : ℚ),(3676079 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX98 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3676077 / 10000000 : ℚ),(3676079 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
