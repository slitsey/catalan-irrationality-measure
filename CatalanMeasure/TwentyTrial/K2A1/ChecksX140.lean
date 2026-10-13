module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX140 : integerGapOK AZX ((4799549 / 5000000 : ℚ),(95991 / 100000 : ℚ),true)=true :=by decide +kernel
theorem bracketX140 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4799549 / 5000000 : ℚ),(95991 / 100000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
