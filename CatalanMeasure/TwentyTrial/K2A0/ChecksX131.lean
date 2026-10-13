module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX131 : integerGapOK AZX ((276877 / 312500 : ℚ),(4430033 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX131 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((276877 / 312500 : ℚ),(4430033 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
