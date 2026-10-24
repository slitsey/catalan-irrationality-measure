module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX5 : integerGapOK AZX ((-522697 / 1250000 : ℚ),(-2090787 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX5 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-522697 / 1250000 : ℚ),(-2090787 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
