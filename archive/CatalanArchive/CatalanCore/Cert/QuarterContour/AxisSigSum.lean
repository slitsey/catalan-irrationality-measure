module
public import CatalanCore.Cert.QuarterContour.FastMacros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.AxisSigSum
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def paired (p q : Pt) : Bool := decide (p.1 = q.1 ∧ p.2.1 = -q.2.1)

lemma qplusN_pair (xl xh : ℤ) (p q : Pt) (hx : p.1 = q.1) (hy : p.2.1 = -q.2.1) :
    SigmaP6.qplusN xl xh 0 0 p = SigmaP6.qplusN xl xh 0 0 q := by
  simp only [SigmaP6.qplusN,zero_sub,Int.natAbs_neg,max_self,hx,hy]

/-- A matching adjacent conjugate pair shares one exact logarithm; all other heads fall back. -/
def axisSum (xl xh : ℤ) : List Pt → ℤ
  | [] => 0
  | [p] => (p.2.2 : ℤ)*QuarterCompute.FastNode.logUp (SigmaP6.qplusN xl xh 0 0 p)
  | p::q::ps =>
    if paired p q then
      ((p.2.2 : ℤ)+(q.2.2 : ℤ))*QuarterCompute.FastNode.logUp (SigmaP6.qplusN xl xh 0 0 p)+axisSum xl xh ps
    else
      (p.2.2 : ℤ)*QuarterCompute.FastNode.logUp (SigmaP6.qplusN xl xh 0 0 p)+axisSum xl xh (q::ps)

lemma axisSum_eq (xl xh : ℤ) (ps : List Pt) :
    axisSum xl xh ps = FastMacros.sigSum xl xh 0 0 ps := by
  induction ps using List.twoStepInduction with
  | nil => rfl
  | singleton p => simp only [axisSum,FastMacros.sigSum,add_zero]
  | cons_cons p q ps ih0 ih1 =>
    rw [axisSum]
    split_ifs with h
    · have hp : p.1 = q.1 ∧ p.2.1 = -q.2.1 := of_decide_eq_true h
      have he := qplusN_pair xl xh p q hp.1 hp.2
      rw [ih0]
      simp only [FastMacros.sigSum,← he]
      ring
    · rw [ih1 q]
      rfl

/-- Non-axis geometry keeps the accepted evaluator unchanged. -/
def sigSum (xl xh yl yh : ℤ) (ps : List Pt) : ℤ :=
  if yl = 0 ∧ yh = 0 then axisSum xl xh ps else FastMacros.sigSum xl xh yl yh ps

lemma sigSum_eq (xl xh yl yh : ℤ) (ps : List Pt) :
    sigSum xl xh yl yh ps = FastMacros.sigSum xl xh yl yh ps := by
  by_cases h : yl = 0 ∧ yh = 0
  · rcases h with ⟨rfl,rfl⟩
    simp only [sigSum,axisSum_eq,ite_self]
  · simp only [sigSum,if_neg h]

def macroLB (pts : List Pt) (m : Macro) (b : Quad) : ℚ :=
  SigmaP6.sigTL m.x0 m.y0 m.fd b.1 b.2.1 b.2.2.1 b.2.2.2
    (sigSum b.1 b.2.1 b.2.2.1 b.2.2.2 (macroNear pts m))

lemma macroLB_eq (pts : List Pt) (m : Macro) (b : Quad) :
    macroLB pts m b = FastMacros.macroLB pts m b := by
  simp only [macroLB,FastMacros.macroLB,sigSum_eq]

def axisOK (pts : List Pt) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b =>
    decide (QuarterCompute.FastAxisNode.axisGeom b) &&
    decide ((b.2.2.2.1 : ℚ)/2^32 ≤ QuarterCompute.FastAxisNode.quarterAxisLB (macroLB pts m b.1)
      (QuarterCompute.FastAxisNode.axisUt b.1.1 b.1.2.1)
      (QuarterCompute.FastAxisNode.axisUt b.2.1 b.2.2.1)))

lemma axisOK_eq_fast (pts : List Pt) (m : Macro) : axisOK pts m = FastMacros.axisOK pts m := by
  simp only [axisOK,FastMacros.axisOK,macroLB_eq]

lemma axisOK_eq (pts : List Pt) (m : Macro) : axisOK pts m = SigmaQuarter.axisOK pts m :=
  (axisOK_eq_fast pts m).trans (FastMacros.axisOK_eq pts m)
end CatalanCore.Cert.QuarterContour.AxisSigSum
#print axioms CatalanCore.Cert.QuarterContour.AxisSigSum.axisSum_eq
#print axioms CatalanCore.Cert.QuarterContour.AxisSigSum.axisOK_eq