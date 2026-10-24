module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX126 : integerGapOK AZX ((4085743 / 5000000 : ℚ),(1687 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX126 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4085743 / 5000000 : ℚ),(1687 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
