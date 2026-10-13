module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX111 : integerGapOK AZX ((36721 / 62500 : ℚ),(5 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX111 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((36721 / 62500 : ℚ),(5 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
