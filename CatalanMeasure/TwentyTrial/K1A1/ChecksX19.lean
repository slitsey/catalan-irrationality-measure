module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX19 : integerGapOK AZX ((-402759 / 1000000 : ℚ),(-1006897 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX19 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-402759 / 1000000 : ℚ),(-1006897 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
