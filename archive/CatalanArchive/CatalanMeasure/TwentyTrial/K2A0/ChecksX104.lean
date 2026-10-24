module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX104 : integerGapOK AZX ((2370607 / 5000000 : ℚ),(148163 / 312500 : ℚ),true)=true :=by decide +kernel
theorem bracketX104 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2370607 / 5000000 : ℚ),(148163 / 312500 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
