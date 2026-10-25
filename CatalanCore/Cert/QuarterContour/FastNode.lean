module
public import CatalanCore.Cert.QuarterContour.TableLog
public import CatalanCore.Cert.QuarterContour.FastAtanTable
public import CatalanCore.Cert.QuarterContour.ModelCellCached
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FastNode
open CatalanLambda.Cert CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval

/-- Exact old logarithms with direct balanced-table reads and primitive divisions. -/
def logLo (N : ℕ) : ℤ := TableLog.lo N (Nat.log2 N)
def logUp (N : ℕ) : ℤ := TableLog.up N (Nat.log2 N)

lemma logLo_eq (N : ℕ) : logLo N = logLoS N := by
  simp only [logLo,TableLog.lo,TableLog.tabLoD,TableLog.tabUpD,
    FastTables.lo_eq,FastTables.up_eq,logLoS,tabLo,tabUp,
    Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
lemma logUp_eq (N : ℕ) : logUp N = logUpS N := by
  simp only [logUp,TableLog.up,TableLog.tabLoD,TableLog.tabUpD,
    FastTables.lo_eq,FastTables.up_eq,logUpS,tabLo,tabUp,
    Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]

def theta (vlo : ℚ) : ℚ :=
  let j := min (⌊vlo*256⌋₊) JM
  (FastAtanTable.value j : ℚ)/2^64 +
    (if j = JM then 0 else (vlo-(j : ℚ)/256)/(1+(((j : ℚ)+1)/256)^2))
lemma theta_eq (vlo : ℚ) : theta vlo = thetaQ vlo := by
  simp only [theta,thetaQ,FastAtanTable.value_eq]

def thetaX (vlo : ℚ) : ℚ :=
  if (JM : ℚ)/256 ≤ vlo then
    (FastAtanTable.value 128 : ℚ)/2^64 + theta ((vlo-1/2)/(1+vlo/2))
  else theta vlo
lemma thetaX_eq (vlo : ℚ) : thetaX vlo = SigmaP6.thetaX vlo := by
  simp only [thetaX,SigmaP6.thetaX,theta_eq,FastAtanTable.value_eq]

def L1 (xlo yhi : ℤ) : ℚ := (logUp (xlo*xlo+yhi*yhi).toNat : ℚ)/2^64
def littleL (xhi ylo : ℤ) : ℚ := (logLo ((2^40-xhi)^2+ylo^2).toNat : ℚ)/2^64
lemma L1_eq (xlo yhi : ℤ) : L1 xlo yhi = SigmaP6.L1Q xlo yhi := by
  simp only [L1,SigmaP6.L1Q,logUp_eq]
lemma littleL_eq (xhi ylo : ℤ) : littleL xhi ylo = SigmaP6.lQ xhi ylo := by
  simp only [littleL,SigmaP6.lQ,logLo_eq]

def boxLBg (Ls : ℚ) (xlo xhi ylo yhi : ℤ) : ℚ :=
  let l1 := L1 xlo yhi
  let Aup : ℚ := (1/2)*qmax ((-(xhi : ℚ)/2^40)*l1) ((-(xlo : ℚ)/2^40)*l1)
  let l := littleL xhi ylo
  let Bup : ℚ := -(1/2)*qmin ((((2 : ℚ)^40-xhi)/2^40)*l)
    ((((2 : ℚ)^40-xlo)/2^40)*l)
  let th := thetaX (vloQ xlo ylo yhi)
  let Cup : ℚ := -qmin ((ylo : ℚ)/2^40*th) ((yhi : ℚ)/2^40*th)
  Ls-(1+Aup+Bup+Cup)+(999/1000)*PILO*((ylo : ℚ)/2^40)
lemma boxLBg_eq (Ls : ℚ) (xlo xhi ylo yhi : ℤ) :
    boxLBg Ls xlo xhi ylo yhi = SigmaP6.boxLBg Ls xlo xhi ylo yhi := by
  simp only [boxLBg,SigmaP6.boxLBg,L1_eq,littleL_eq,thetaX_eq]

def logThreeHalfLo : ℚ := (logLo (3*2^79) : ℚ)/2^64
lemma logThreeHalfLo_eq : logThreeHalfLo = SigmaQuarter.logThreeHalfLo := by
  simp only [logThreeHalfLo,SigmaQuarter.logThreeHalfLo,logLo_eq]

def quarterBoxLB (epsilon Ls : ℚ) (xl xh yl yh al ah bl bh : ℤ) : ℚ :=
  (5/4)*Ls+(1/2)*boxLBg 0 xl xh yl yh+(3/4)*boxLBg 0 al ah bl bh+
    (3/4)*logThreeHalfLo+(1/1000-epsilon)*PILO*((yl : ℚ)/2^40)
lemma quarterBoxLB_eq (epsilon Ls : ℚ) (xl xh yl yh al ah bl bh : ℤ) :
    quarterBoxLB epsilon Ls xl xh yl yh al ah bl bh =
      QuarterContour.quarterBoxLB epsilon Ls xl xh yl yh al ah bl bh := by
  simp only [quarterBoxLB,QuarterContour.quarterBoxLB,SigmaQuarter.quarterBoxLB,
    boxLBg_eq,logThreeHalfLo_eq]

def nodeOK (epsilon mp : ℚ) (p : QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (b : QBox) : Bool :=
  decide (boxGeom b) &&
  decide (-H ≤ (vInterval p b.1.2.2.1 b.1.2.2.2).1 ∧
    (vInterval p b.1.2.2.1 b.1.2.2.2).2 ≤ H) &&
  decide (mp ≤ quarterBoxLB epsilon
    ((sigmaLower p cs denom base error b.1.2.2.1 b.1.2.2.2 : ℤ)/(2^48 : ℚ))
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2)
lemma nodeOK_eq (epsilon mp : ℚ) (p : QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (b : QBox) :
    nodeOK epsilon mp p cs denom base error b =
      ModelCellNode.nodeOK epsilon mp p cs denom base error b := by
  simp only [nodeOK,ModelCellNode.nodeOK,quarterBoxLB_eq]

def nodeOKCached (epsilon mp : ℚ) (p : QuarterCompute.Model.Params)
    (cints : List Interval) (base : ℤ) (error : ℕ) (b : QBox) : Bool :=
  decide (boxGeom b) &&
  decide (-H ≤ (vInterval p b.1.2.2.1 b.1.2.2.2).1 ∧
    (vInterval p b.1.2.2.1 b.1.2.2.2).2 ≤ H) &&
  decide (mp ≤ quarterBoxLB epsilon
    ((QuarterCompute.ModelCellCached.sigmaLower p cints base error
      b.1.2.2.1 b.1.2.2.2 : ℤ)/(2^48 : ℚ))
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2)
lemma nodeOKCached_eq_cached (epsilon mp : ℚ) (p : QuarterCompute.Model.Params)
    (cints : List Interval) (base : ℤ) (error : ℕ) (b : QBox) :
    nodeOKCached epsilon mp p cints base error b =
      ModelCellCached.nodeOK epsilon mp p cints base error b := by
  simp only [nodeOKCached,ModelCellCached.nodeOK,quarterBoxLB_eq]
lemma nodeOKCached_eq (epsilon mp : ℚ) (p : QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (cints : List Interval) (base : ℤ) (error : ℕ) (b : QBox)
    (hc : cints = coefficients H (denom : ℤ) cs) :
    nodeOKCached epsilon mp p cints base error b =
      ModelCellNode.nodeOK epsilon mp p cs denom base error b := by
  rw [nodeOKCached_eq_cached,ModelCellCached.nodeOK_eq epsilon mp p cs denom cints base error b hc]
end CatalanCore.Cert.QuarterContour.FastNode
#print axioms CatalanCore.Cert.QuarterContour.FastNode.quarterBoxLB_eq
#print axioms CatalanCore.Cert.QuarterContour.FastNode.nodeOK_eq
#print axioms CatalanCore.Cert.QuarterContour.FastNode.nodeOKCached_eq
