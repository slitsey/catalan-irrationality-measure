module
public import CatalanCore.Cert.QuarterCompute.PolyCells2
public import CatalanCore.Cert.QuarterContour.FastNode
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.PolyModel2.FastCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def coefficientIntervals : List (Int × Int) := [(0,1),(-190398731467,-190398731466),(-360483166,-360483165),(211333884,211333885),(296125268,296125269),(-275587745,-275587744),(8960985,8960986),(51008688,51008689),(-6711539,-6711538),(-6573095,-6573094),(1381699,1381700),(621189,621190),(-253286,-253285),(-26636,-26635),(43477,43478),(-4919,-4918),(-14261,-14260),(21973,21974),(-34002,-34001),(34357,34358),(-31248,-31247),(17740,17741),(-11037,-11036),(3303,3304),(-1831,-1830),(139,140),(-162,-161),(-16,-15),(-8,-7),(-1,0),(-1,0)]
theorem coefficientIntervals_checked : coefficientIntervals = DyadicInterval.coefficients ModelCell.H (ModelFactors.denominator : Int) coefficients := by decide +kernel
theorem fastCheckedPart0 : cellsPart0.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart1 : cellsPart1.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart2 : cellsPart2.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart3 : cellsPart3.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart4 : cellsPart4.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart5 : cellsPart5.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart6 : cellsPart6.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart7 : cellsPart7.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart8 : cellsPart8.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart9 : cellsPart9.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fastCheckedPart10 : cellsPart10.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fast_cells_checked : cells.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by
  simp only [cells,List.all_append,fastCheckedPart0,fastCheckedPart1,fastCheckedPart2,fastCheckedPart3,fastCheckedPart4,fastCheckedPart5,fastCheckedPart6,fastCheckedPart7,fastCheckedPart8,fastCheckedPart9,fastCheckedPart10,Bool.true_and]
theorem cells_checked : cells.all (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) = true := by
  have he : (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) := by
    funext b
    exact QuarterContour.FastNode.nodeOKCached_eq (1/100000) (115867/50000) params coefficients ModelFactors.denominator coefficientIntervals baseUpper errorUpper b coefficientIntervals_checked
  rw [← he]
  exact fast_cells_checked
end CatalanCore.Cert.QuarterCompute.PolyModel2.FastCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.FastCells.coefficientIntervals_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.FastCells.fast_cells_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.FastCells.cells_checked
