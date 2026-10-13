module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX12 : integerGapOK AZX ((-4986393 / 5000000 : ℚ),(-623299 / 625000 : ℚ),true)=true :=by decide +kernel
theorem bracketX12 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4986393 / 5000000 : ℚ),(-623299 / 625000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
