module
public import CatalanCore.Cert.QuarterCompute.PolyModel2
public import CatalanCore.Cert.QuarterCompute.PolyCellData2
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells
open CatalanCore.Cert.QuarterCompute.PolyCellData2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def coefficientIntervals : List (Int × Int) := [(0,1),(-190398731467,-190398731466),(-360483166,-360483165),(211333884,211333885),(296125268,296125269),(-275587745,-275587744),(8960985,8960986),(51008688,51008689),(-6711539,-6711538),(-6573095,-6573094),(1381699,1381700),(621189,621190),(-253286,-253285),(-26636,-26635),(43477,43478),(-4919,-4918),(-14261,-14260),(21973,21974),(-34002,-34001),(34357,34358),(-31248,-31247),(17740,17741),(-11037,-11036),(3303,3304),(-1831,-1830),(139,140),(-162,-161),(-16,-15),(-8,-7),(-1,0),(-1,0)]
theorem coefficientIntervals_checked : coefficientIntervals = DyadicInterval.coefficients ModelCell.H (ModelFactors.denominator : Int) coefficients := by decide +kernel
theorem checkedPart0 : cellsPart0.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart1 : cellsPart1.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart2 : cellsPart2.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart3 : cellsPart3.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart4 : cellsPart4.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart5 : cellsPart5.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart6 : cellsPart6.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart7 : cellsPart7.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart8 : cellsPart8.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart9 : cellsPart9.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart10 : cellsPart10.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem cells_checked : cells.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by
  simp only [cells,List.all_append,checkedPart0,checkedPart1,checkedPart2,checkedPart3,checkedPart4,checkedPart5,checkedPart6,checkedPart7,checkedPart8,checkedPart9,checkedPart10,Bool.true_and]
theorem cells_length : cells.length = 704 := by decide +kernel
end CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells.coefficientIntervals_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells.cells_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells.cells_length
