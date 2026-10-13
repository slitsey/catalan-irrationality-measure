module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX46 : integerGapOK AZX ((1148537 / 5000000 : ℚ),(574269 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX46 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1148537 / 5000000 : ℚ),(574269 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
