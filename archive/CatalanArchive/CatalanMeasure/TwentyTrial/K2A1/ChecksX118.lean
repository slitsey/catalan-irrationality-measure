module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX118 : integerGapOK AZX ((719 / 1000 : ℚ),(366963 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX118 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((719 / 1000 : ℚ),(366963 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
