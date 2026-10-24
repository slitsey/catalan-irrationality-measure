module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX110 : integerGapOK AZX ((2937679 / 5000000 : ℚ),(36721 / 62500 : ℚ),true)=true :=by decide +kernel
theorem bracketX110 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2937679 / 5000000 : ℚ),(36721 / 62500 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
