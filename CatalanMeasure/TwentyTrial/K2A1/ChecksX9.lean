module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX9 : integerGapOK AZX ((-999189 / 1000000 : ℚ),(-49951 / 50000 : ℚ),false)=true :=by decide +kernel
theorem bracketX9 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-999189 / 1000000 : ℚ),(-49951 / 50000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
