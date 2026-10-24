module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX123 : integerGapOK AZX ((3888941 / 5000000 : ℚ),(203 / 250 : ℚ),false)=true :=by decide +kernel
theorem bracketX123 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3888941 / 5000000 : ℚ),(203 / 250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
