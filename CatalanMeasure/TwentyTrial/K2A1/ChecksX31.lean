module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX31 : integerGapOK AZX ((-9107179 / 10000000 : ℚ),(-1813 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX31 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9107179 / 10000000 : ℚ),(-1813 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
