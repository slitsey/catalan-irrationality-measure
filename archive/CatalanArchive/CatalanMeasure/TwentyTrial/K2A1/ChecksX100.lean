module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX100 : integerGapOK AZX ((3 / 8 : ℚ),(2131693 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX100 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3 / 8 : ℚ),(2131693 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
