module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX84 : integerGapOK AZX ((280913 / 2000000 : ℚ),(313 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX84 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((280913 / 2000000 : ℚ),(313 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
