module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX65 : integerGapOK AZX ((1422719 / 2500000 : ℚ),(1187 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX65 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1422719 / 2500000 : ℚ),(1187 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
