module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX25 : integerGapOK AZX ((-198629 / 625000 : ℚ),(-1589031 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX25 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-198629 / 625000 : ℚ),(-1589031 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
