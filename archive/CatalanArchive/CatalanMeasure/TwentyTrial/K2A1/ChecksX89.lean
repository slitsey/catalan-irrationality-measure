module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX89 : integerGapOK AZX ((219489 / 1000000 : ℚ),(548723 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX89 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((219489 / 1000000 : ℚ),(548723 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
