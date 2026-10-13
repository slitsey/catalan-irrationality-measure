module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX61 : integerGapOK AZX ((438823 / 625000 : ℚ),(7021171 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX61 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((438823 / 625000 : ℚ),(7021171 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
