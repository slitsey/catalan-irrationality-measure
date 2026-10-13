module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX147 : integerGapOK AZX ((2461669 / 2500000 : ℚ),(19767 / 20000 : ℚ),false)=true :=by decide +kernel
theorem bracketX147 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2461669 / 2500000 : ℚ),(19767 / 20000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
