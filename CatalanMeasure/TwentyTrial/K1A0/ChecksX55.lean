module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX55 : integerGapOK AZX ((618833 / 1000000 : ℚ),(6188333 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX55 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((618833 / 1000000 : ℚ),(6188333 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
