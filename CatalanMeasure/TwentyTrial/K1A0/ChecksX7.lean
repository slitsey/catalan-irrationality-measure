module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX7 : integerGapOK AZX ((-813 / 2000 : ℚ),(-944589 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX7 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-813 / 2000 : ℚ),(-944589 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
