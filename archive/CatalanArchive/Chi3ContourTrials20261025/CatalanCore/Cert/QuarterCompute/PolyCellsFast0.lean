module
public import CatalanCore.Cert.QuarterCompute.PolyCells0
public import CatalanCore.Cert.QuarterContour.FastNode
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.PolyModel0.FastCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def coefficientIntervals : List (Int × Int) := [(0,1),(-198321958438,-198321958437),(-31906565763,-31906565762),(15566881184,15566881185),(-900190817,-900190816),(-1340246846,-1340246845),(460759785,460759786),(23622765,23622766),(-68661934,-68661933),(18018775,18018776),(3972676,3972677),(-3831213,-3831212),(651823,651824),(357794,357795),(-213951,-213950),(15543,15544),(21444,21445),(-9246,-9245),(-40767,-40766),(-54677,-54676),(-97888,-97887),(-100245,-100244),(-81560,-81559),(-49116,-49115),(-22492,-22491),(-7615,-7614),(-1900,-1899),(-337,-336),(-41,-40),(-3,-2),(-1,0)]
theorem coefficientIntervals_checked : coefficientIntervals = DyadicInterval.coefficients ModelCell.H (ModelFactors.denominator : Int) coefficients := by decide +kernel
theorem fastCheckedPart0 : cellsPart0.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem fast_cells_checked : cells.all (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by
  simp only [cells,List.all_append,fastCheckedPart0,Bool.true_and]
theorem cells_checked : cells.all (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) = true := by
  have he : (QuarterContour.FastNode.nodeOKCached (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) := by
    funext b
    exact QuarterContour.FastNode.nodeOKCached_eq (1/100000) (115867/50000) params coefficients ModelFactors.denominator coefficientIntervals baseUpper errorUpper b coefficientIntervals_checked
  rw [← he]
  exact fast_cells_checked
end CatalanCore.Cert.QuarterCompute.PolyModel0.FastCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel0.FastCells.coefficientIntervals_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel0.FastCells.fast_cells_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel0.FastCells.cells_checked
