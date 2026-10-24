module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX143 : integerGapOK AZX ((607977 / 625000 : ℚ),(4863817 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX143 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((607977 / 625000 : ℚ),(4863817 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
