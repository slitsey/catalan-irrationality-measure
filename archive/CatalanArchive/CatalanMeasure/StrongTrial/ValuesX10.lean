module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_101 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-6262509971 / 10000000000 : ℚ),(-391406873 / 625000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_103 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-190968971 / 312500000 : ℚ),(-6111007069 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_105 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1191807127 / 2000000000 : ℚ),(-372439727 / 625000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_107 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-5803291617 / 10000000000 : ℚ),(-2901645807 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_109 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-5647704447 / 10000000000 : ℚ),(-1411926111 / 2500000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
