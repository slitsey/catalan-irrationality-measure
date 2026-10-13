module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX125 : integerGapOK AZX ((2042871 / 2500000 : ℚ),(4085743 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX125 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2042871 / 2500000 : ℚ),(4085743 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
