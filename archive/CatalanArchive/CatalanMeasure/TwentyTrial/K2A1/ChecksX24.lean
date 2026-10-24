module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX24 : integerGapOK AZX ((-4779957 / 5000000 : ℚ),(-9559911 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX24 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4779957 / 5000000 : ℚ),(-9559911 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
