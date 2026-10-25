module
public import CatalanCore.Cert.QuarterCompute.PolyModel1
public import CatalanCore.Cert.QuarterCompute.PolyCellData1
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells
open CatalanCore.Cert.QuarterCompute.PolyCellData1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def coefficientIntervals : List (Int × Int) := [(0,1),(-197903363605,-197903363604),(8102334443,8102334444),(-587477545,-587477544),(-1031951180,-1031951179),(189729957,189729958),(23957414,23957415),(11417478,11417479),(-1124020,-1124019),(-1816120,-1816119),(-240817,-240816),(40416,40417),(53027,53028),(11675,11676),(-2143,-2142),(-1787,-1786),(-19907,-19906),(-20739,-20738),(-57469,-57468),(7260,7261),(-33950,-33949),(13952,13953),(-9195,-9194),(3242,3243),(-1050,-1049),(238,239),(-44,-43),(5,6),(-1,0),(0,1),(-1,0)]
theorem coefficientIntervals_checked : coefficientIntervals = DyadicInterval.coefficients ModelCell.H (ModelFactors.denominator : Int) coefficients := by decide +kernel
theorem checkedPart0 : cellsPart0.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart1 : cellsPart1.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart2 : cellsPart2.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem checkedPart3 : cellsPart3.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by decide +kernel
theorem cells_checked : cells.all (FastNode.nodeOK (1/100000) (115867/50000) params coefficientIntervals baseUpper errorUpper) = true := by
  simp only [cells,List.all_append,checkedPart0,checkedPart1,checkedPart2,checkedPart3,Bool.true_and]
theorem cells_length : cells.length = 256 := by decide +kernel
end CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells.coefficientIntervals_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells.cells_checked
#print axioms CatalanCore.Cert.QuarterCompute.PolyModel1.PureCells.cells_length
