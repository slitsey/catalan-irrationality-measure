module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_21 : shiftedColumnBracketOK C Vc V AY QY MY ((799042721 / 5000000000 : ℚ),(319617089 / 2000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_23 : shiftedColumnBracketOK C Vc V AY QY MY ((442437277 / 2500000000 : ℚ),(1769749111 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_25 : shiftedColumnBracketOK C Vc V AY QY MY ((61059259 / 312500000 : ℚ),(1953896291 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_27 : shiftedColumnBracketOK C Vc V AY QY MY ((531980419 / 2500000000 : ℚ),(2127921679 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_29 : shiftedColumnBracketOK C Vc V AY QY MY ((2311831969 / 10000000000 : ℚ),(577957993 / 2500000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
