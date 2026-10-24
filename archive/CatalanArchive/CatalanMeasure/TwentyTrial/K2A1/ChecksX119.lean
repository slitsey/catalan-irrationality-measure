module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX119 : integerGapOK AZX ((366963 / 500000 : ℚ),(3669631 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX119 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((366963 / 500000 : ℚ),(3669631 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
