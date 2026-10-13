module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX60 : integerGapOK AZX ((86 / 125 : ℚ),(438823 / 625000 : ℚ),false)=true :=by decide +kernel
theorem bracketX60 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((86 / 125 : ℚ),(438823 / 625000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
