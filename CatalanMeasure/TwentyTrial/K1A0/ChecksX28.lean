module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX28 : integerGapOK AZX ((1268369 / 10000000 : ℚ),(1268371 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX28 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1268369 / 10000000 : ℚ),(1268371 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
