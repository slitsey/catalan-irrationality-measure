module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX149 : integerGapOK AZX ((1979943 / 2000000 : ℚ),(9899717 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX149 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1979943 / 2000000 : ℚ),(9899717 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
