module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX6 : integerGapOK AZX ((-2090787 / 5000000 : ℚ),(-813 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX6 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2090787 / 5000000 : ℚ),(-813 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
