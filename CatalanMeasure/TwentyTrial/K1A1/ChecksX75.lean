module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX75 : integerGapOK AZX ((719 / 1000 : ℚ),(184729 / 250000 : ℚ),false)=true :=by decide +kernel
theorem bracketX75 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((719 / 1000 : ℚ),(184729 / 250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
