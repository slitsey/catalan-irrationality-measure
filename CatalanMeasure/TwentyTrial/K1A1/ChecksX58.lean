module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX58 : integerGapOK AZX ((4600217 / 10000000 : ℚ),(4600219 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX58 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4600217 / 10000000 : ℚ),(4600219 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
