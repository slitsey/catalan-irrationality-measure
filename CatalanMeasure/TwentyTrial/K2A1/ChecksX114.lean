module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX114 : integerGapOK AZX ((1597849 / 2500000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketX114 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1597849 / 2500000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
