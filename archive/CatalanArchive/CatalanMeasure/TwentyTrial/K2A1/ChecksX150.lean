module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX150 : integerGapOK AZX ((9899717 / 10000000 : ℚ),(4961 / 5000 : ℚ),false)=true :=by decide +kernel
theorem bracketX150 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((9899717 / 10000000 : ℚ),(4961 / 5000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
