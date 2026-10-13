module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX133 : integerGapOK AZX ((1813 / 2000 : ℚ),(458657 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX133 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1813 / 2000 : ℚ),(458657 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
