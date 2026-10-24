module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX96 : integerGapOK AZX ((1568857 / 5000000 : ℚ),(687 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX96 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1568857 / 5000000 : ℚ),(687 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
