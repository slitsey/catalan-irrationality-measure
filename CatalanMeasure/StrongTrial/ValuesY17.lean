module
public import CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_171 : shiftedColumnBracketOK C Vc V AY QY MY ((9998114773 / 10000000000 : ℚ),(1249764347 / 1250000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_173 : shiftedColumnBracketOK C Vc V AY QY MY ((499950887 / 500000000 : ℚ),(9999017743 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
