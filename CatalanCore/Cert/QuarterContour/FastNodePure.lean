module
public import CatalanCore.Cert.QuarterCompute.FastNode
public import CatalanCore.Cert.QuarterContour.FastNode
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FastNodePure
open CatalanCore.Cert.QuarterCompute
open CatalanLambda.Cert CatalanCore.Cert.SigmaP6
set_option maxRecDepth 100000

lemma lo_eq (j : ℕ) : FastTableData.lo j = FastTables.lo j := by
  by_cases hj : j < 257
  · simp only [FastTableData.lo,FastTables.lo,if_pos hj]
  · simp only [FastTableData.lo,FastTables.lo,if_neg hj,CatalanLambda.Cert.tabLo,Nat.shiftRight_eq_div_pow]
lemma up_eq (j : ℕ) : FastTableData.up j = FastTables.up j := by
  by_cases hj : j < 257
  · simp only [FastTableData.up,FastTables.up,if_pos hj]
  · simp only [FastTableData.up,FastTables.up,if_neg hj,CatalanLambda.Cert.tabUp,Nat.shiftRight_eq_div_pow]
lemma atan_eq (j : ℕ) : FastTableData.atan j = FastAtanTable.value j := by rfl

lemma logLo_eq (N : ℕ) : QuarterCompute.FastNode.logLo N = QuarterContour.FastNode.logLo N := by
  simp only [QuarterCompute.FastNode.logLo,QuarterContour.FastNode.logLo,TableLog.lo,
    TableLog.tabLoD,TableLog.tabUpD,lo_eq,up_eq]
lemma logUp_eq (N : ℕ) : QuarterCompute.FastNode.logUp N = QuarterContour.FastNode.logUp N := by
  simp only [QuarterCompute.FastNode.logUp,QuarterContour.FastNode.logUp,TableLog.up,
    TableLog.tabLoD,TableLog.tabUpD,lo_eq,up_eq]
lemma theta_eq (v : ℚ) : QuarterCompute.FastNode.theta v = QuarterContour.FastNode.theta v := by
  simp only [QuarterCompute.FastNode.theta,QuarterContour.FastNode.theta,atan_eq,JM]
  rfl
lemma thetaX_eq (v : ℚ) : QuarterCompute.FastNode.thetaX v = QuarterContour.FastNode.thetaX v := by
  simp only [QuarterCompute.FastNode.thetaX,QuarterContour.FastNode.thetaX,atan_eq,theta_eq,JM]
  rfl
lemma L1_eq (x y : ℤ) : QuarterCompute.FastNode.L1 x y = QuarterContour.FastNode.L1 x y := by
  simp only [QuarterCompute.FastNode.L1,QuarterContour.FastNode.L1,logUp_eq]
lemma littleL_eq (x y : ℤ) : QuarterCompute.FastNode.littleL x y = QuarterContour.FastNode.littleL x y := by
  simp only [QuarterCompute.FastNode.littleL,QuarterContour.FastNode.littleL,logLo_eq]
lemma boxLBg_eq (L : ℚ) (xl xh yl yh : ℤ) :
    QuarterCompute.FastNode.boxLBg L xl xh yl yh = QuarterContour.FastNode.boxLBg L xl xh yl yh := by
  simp only [QuarterCompute.FastNode.boxLBg,QuarterContour.FastNode.boxLBg,L1_eq,littleL_eq,thetaX_eq,
    QuarterCompute.FastNode.vlo,SigmaP6.vloQ,QuarterCompute.FastNode.qmin,SigmaP6.qmin,
    QuarterCompute.FastNode.qmax,SigmaP6.qmax,QuarterCompute.FastNode.PILO,SigmaP6.PILO]
  rfl
lemma quarterBoxLB_eq (epsilon L : ℚ) (xl xh yl yh al ah bl bh : ℤ) :
    QuarterCompute.FastNode.quarterBoxLB epsilon L xl xh yl yh al ah bl bh =
      QuarterContour.FastNode.quarterBoxLB epsilon L xl xh yl yh al ah bl bh := by
  simp only [QuarterCompute.FastNode.quarterBoxLB,QuarterContour.FastNode.quarterBoxLB,boxLBg_eq,
    QuarterCompute.FastNode.logThreeHalfLo,QuarterContour.FastNode.logThreeHalfLo,logLo_eq,
    QuarterCompute.FastNode.PILO,SigmaP6.PILO]
lemma boxGeom_eq (b : QuarterCompute.FastNode.QBox) :
    QuarterCompute.FastNode.boxGeom b = SigmaQuarter.boxGeom b := by rfl
lemma nodeOK_eq (epsilon mp : ℚ) (p : Model.Params)
    (cints : List DyadicInterval.Interval) (base : ℤ) (error : ℕ) (b : QuarterCompute.FastNode.QBox) :
    QuarterCompute.FastNode.nodeOK epsilon mp p cints base error b =
      QuarterContour.FastNode.nodeOKCached epsilon mp p cints base error b := by
  simp only [QuarterCompute.FastNode.nodeOK,QuarterContour.FastNode.nodeOKCached,boxGeom_eq,quarterBoxLB_eq]
end CatalanCore.Cert.QuarterContour.FastNodePure
#print axioms CatalanCore.Cert.QuarterContour.FastNodePure.nodeOK_eq
