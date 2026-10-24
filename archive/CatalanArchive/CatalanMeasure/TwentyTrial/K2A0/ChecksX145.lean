module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX145 : integerGapOK AZX ((1221 / 1250 : ℚ),(491641 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX145 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1221 / 1250 : ℚ),(491641 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
