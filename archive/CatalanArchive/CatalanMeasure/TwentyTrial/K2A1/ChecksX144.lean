module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX144 : integerGapOK AZX ((4863817 / 5000000 : ℚ),(1969 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX144 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4863817 / 5000000 : ℚ),(1969 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
