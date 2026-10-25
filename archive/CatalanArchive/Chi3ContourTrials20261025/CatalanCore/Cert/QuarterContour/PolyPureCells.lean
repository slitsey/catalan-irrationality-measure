module
public import CatalanCore.Cert.QuarterCompute.PolyCellsPure0
public import CatalanCore.Cert.QuarterCompute.PolyCellsPure1
public import CatalanCore.Cert.QuarterCompute.PolyCellsPure2
public import CatalanCore.Cert.QuarterContour.FastNodePure
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.PolyModel0.PureCells
theorem original_cells_checked : PolyCellData0.cells.all (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) = true := by
  have he : (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) =
    (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) := by
    funext b
    rw [QuarterContour.FastNodePure.nodeOK_eq]
    exact QuarterContour.FastNode.nodeOKCached_eq (1/100000) (115867/50000) params coefficients ModelFactors.denominator coefficientIntervals baseUpper errorUpper b coefficientIntervals_checked
  rw [← he]
  exact cells_checked
end CatalanCore.Cert.QuarterCompute.PolyModel0.PureCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel0.PureCells.original_cells_checked
namespace CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells
theorem original_cells_checked : PolyCellData1.cells.all (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) = true := by
  have he : (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) =
    (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) := by
    funext b
    rw [QuarterContour.FastNodePure.nodeOK_eq]
    exact QuarterContour.FastNode.nodeOKCached_eq (1/100000) (115867/50000) params coefficients ModelFactors.denominator coefficientIntervals baseUpper errorUpper b coefficientIntervals_checked
  rw [← he]
  exact cells_checked
end CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells.original_cells_checked
namespace CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells
theorem original_cells_checked : PolyCellData2.cells.all (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) = true := by
  have he : (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) =
    (QuarterContour.ModelCellNode.nodeOK (1/100000) (115867/50000) params coefficients ModelFactors.denominator baseUpper errorUpper) := by
    funext b
    rw [QuarterContour.FastNodePure.nodeOK_eq]
    exact QuarterContour.FastNode.nodeOKCached_eq (1/100000) (115867/50000) params coefficients ModelFactors.denominator coefficientIntervals baseUpper errorUpper b coefficientIntervals_checked
  rw [← he]
  exact cells_checked
end CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel2.PureCells.original_cells_checked
