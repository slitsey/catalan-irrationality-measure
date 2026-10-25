module
public import CatalanCore.Cert.QuarterCompute.FastAxisNode
public import CatalanCore.Cert.QuarterContour.FastNodePure
public import CatalanCore.Cert.SigmaQuarter.Macros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FastAxisNodePure
open CatalanCore.Cert.QuarterCompute

lemma qmax4_eq (a b c d : ℚ) : FastAxisNode.qmax4 a b c d = SigmaP6.qmax4 a b c d := by rfl
lemma lloQ_eq (N : ℕ) : FastAxisNode.lloQ N = SigmaP6.lloQ N := by
  simp only [FastAxisNode.lloQ,SigmaP6.lloQ,FastNodePure.logLo_eq,QuarterContour.FastNode.logLo_eq]
lemma lupQ_eq (N : ℕ) : FastAxisNode.lupQ N = SigmaP6.lupQ N := by
  simp only [FastAxisNode.lupQ,SigmaP6.lupQ,FastNodePure.logUp_eq,QuarterContour.FastNode.logUp_eq]
lemma F1A_eq (a b : ℤ) : FastAxisNode.F1A a b = SigmaP6.F1A a b := by
  simp only [FastAxisNode.F1A,SigmaP6.F1A,qmax4_eq,lloQ_eq,lupQ_eq]
lemma F2A_eq (b : ℤ) : FastAxisNode.F2A b = SigmaP6.F2A b := by
  simp only [FastAxisNode.F2A,SigmaP6.F2A,lloQ_eq]
lemma utA_eq (a b : ℤ) : FastAxisNode.utA a b = SigmaP6.utA a b := by
  simp only [FastAxisNode.utA,SigmaP6.utA,F1A_eq,F2A_eq]
lemma tlogUB_eq (a b : ℤ) : FastAxisNode.tlogUB a b = SigmaP6.tlogUB a b := by
  simp only [FastAxisNode.tlogUB,SigmaP6.tlogUB,qmax4_eq,lloQ_eq,lupQ_eq]
lemma utB_eq (a b : ℤ) : FastAxisNode.utB a b = SigmaP6.utB a b := by
  simp only [FastAxisNode.utB,SigmaP6.utB,tlogUB_eq]
lemma axisUt_eq (a b : ℤ) : FastAxisNode.axisUt a b = SigmaQuarter.axisUt a b := by
  simp only [FastAxisNode.axisUt,SigmaQuarter.axisUt,utA_eq,utB_eq]
lemma axisGeom_eq (b : QuarterCompute.FastNode.QBox) : FastAxisNode.axisGeom b = SigmaQuarter.axisGeom b := by rfl
lemma quarterAxisLB_eq (Ls u1 u2 : ℚ) :
    FastAxisNode.quarterAxisLB Ls u1 u2 = SigmaQuarter.quarterAxisLB Ls u1 u2 := by
  simp only [FastAxisNode.quarterAxisLB,SigmaQuarter.quarterAxisLB,
    QuarterCompute.FastNode.logThreeHalfLo,SigmaQuarter.logThreeHalfLo,
    FastNodePure.logLo_eq,QuarterContour.FastNode.logLo_eq]
end CatalanCore.Cert.QuarterContour.FastAxisNodePure
#print axioms CatalanCore.Cert.QuarterContour.FastAxisNodePure.quarterAxisLB_eq
