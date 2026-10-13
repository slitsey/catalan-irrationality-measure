module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX29 : integerGapOK AZX ((-4611 / 5000 : ℚ),(-4553591 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX29 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4611 / 5000 : ℚ),(-4553591 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
