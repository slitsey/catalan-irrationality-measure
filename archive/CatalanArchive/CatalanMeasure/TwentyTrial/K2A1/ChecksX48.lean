module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX48 : integerGapOK AZX ((-3336481 / 5000000 : ℚ),(-20853 / 31250 : ℚ),true)=true :=by decide +kernel
theorem bracketX48 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-3336481 / 5000000 : ℚ),(-20853 / 31250 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
