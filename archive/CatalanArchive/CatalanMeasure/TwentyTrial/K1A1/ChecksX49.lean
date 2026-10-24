module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX49 : integerGapOK AZX ((282537 / 1000000 : ℚ),(706343 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX49 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((282537 / 1000000 : ℚ),(706343 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
