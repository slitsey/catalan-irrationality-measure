module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX145 : integerGapOK AZX ((1969 / 2000 : ℚ),(9846673 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX145 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1969 / 2000 : ℚ),(9846673 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
