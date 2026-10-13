module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX8 : integerGapOK AZX ((-2497973 / 2500000 : ℚ),(-999189 / 1000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX8 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2497973 / 2500000 : ℚ),(-999189 / 1000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
