module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX86 : integerGapOK AZX ((1644861 / 10000000 : ℚ),(1644863 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX86 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1644861 / 10000000 : ℚ),(1644863 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
