module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX28 : integerGapOK AZX ((-1872017 / 2000000 : ℚ),(-4611 / 5000 : ℚ),false)=true :=by decide +kernel
theorem bracketX28 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1872017 / 2000000 : ℚ),(-4611 / 5000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
