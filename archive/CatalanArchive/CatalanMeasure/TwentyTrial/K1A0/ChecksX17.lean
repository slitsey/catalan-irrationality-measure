module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX17 : integerGapOK AZX ((-2212901 / 10000000 : ℚ),(-2212899 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX17 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2212901 / 10000000 : ℚ),(-2212899 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
