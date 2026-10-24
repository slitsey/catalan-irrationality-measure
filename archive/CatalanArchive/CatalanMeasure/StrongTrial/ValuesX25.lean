module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_252 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((8068733511 / 10000000000 : ℚ),(4034366757 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_254 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4089561577 / 5000000000 : ℚ),(8179123157 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_256 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((8286342463 / 10000000000 : ℚ),(4143171233 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_258 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((8391498567 / 10000000000 : ℚ),(839149857 / 1000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_260 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((33971209 / 40000000 : ℚ),(8492802253 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
