module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX148 : integerGapOK AZX ((19767 / 20000 : ℚ),(1979943 / 2000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX148 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((19767 / 20000 : ℚ),(1979943 / 2000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
