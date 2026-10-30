module
public import CatalanCore.Cert.QuarterContour.FastNodePure
public import CatalanCore.Cert.QuarterContour.FastAxisNodePure
public import CatalanCore.Cert.QuarterContour.Macros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FastMacros
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

lemma logUp_eq (N : ℕ) : QuarterCompute.FastNode.logUp N = CatalanLambda.Cert.logUpS N :=
  (FastNodePure.logUp_eq N).trans (QuarterContour.FastNode.logUp_eq N)

def sigSum (xl xh yl yh : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*QuarterCompute.FastNode.logUp (SigmaP6.qplusN xl xh yl yh p)+sigSum xl xh yl yh ps

lemma sigSum_eq (xl xh yl yh : ℤ) (ps : List Pt) :
    sigSum xl xh yl yh ps = SigmaP6.sigSum xl xh yl yh ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [sigSum,SigmaP6.sigSum,logUp_eq,ih]

def farTerm (x0 y0 : ℤ) (p : Pt) : FD :=
  ((p.2.2 : ℤ)*QuarterCompute.FastNode.logUp (SigmaP6.farQ x0 y0 p),
   (p.2.2 : ℤ)*(x0-p.1)*(SigmaP6.farLo x0 y0 p : ℤ),
   (p.2.2 : ℤ)*((x0-p.1).natAbs : ℤ),
   (p.2.2 : ℤ)*(y0-p.2.1)*(SigmaP6.farLo x0 y0 p : ℤ),
   (p.2.2 : ℤ)*((y0-p.2.1).natAbs : ℤ),
   (p.2.2 : ℤ)*((SigmaP6.farLo x0 y0 p : ℤ)+1))

lemma farTerm_eq (x0 y0 : ℤ) (p : Pt) : farTerm x0 y0 p = SigmaP6.farTerm x0 y0 p := by
  simp only [farTerm,SigmaP6.farTerm,logUp_eq]

def farSum (x0 y0 : ℤ) : List Pt → FD
  | [] => (0,0,0,0,0,0)
  | p::ps => SigmaP6.fdAdd (farTerm x0 y0 p) (farSum x0 y0 ps)

lemma farSum_eq (x0 y0 : ℤ) (ps : List Pt) : farSum x0 y0 ps = SigmaP6.farSum x0 y0 ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [farSum,SigmaP6.farSum,farTerm_eq,ih]

def farOK (pts : List Pt) (m : Macro) : Prop := farSum m.x0 m.y0 (macroFar pts m) = m.fd
instance (pts : List Pt) (m : Macro) : Decidable (farOK pts m) := by unfold farOK;infer_instance

lemma farOK_eq (pts : List Pt) (m : Macro) : farOK pts m = SigmaQuarter.farOK pts m := by
  simp only [farOK,SigmaQuarter.farOK,farSum_eq]

def macroLB (pts : List Pt) (m : Macro) (b : Quad) : ℚ :=
  SigmaP6.sigTL m.x0 m.y0 m.fd b.1 b.2.1 b.2.2.1 b.2.2.2
    (sigSum b.1 b.2.1 b.2.2.1 b.2.2.2 (macroNear pts m))

lemma macroLB_eq (pts : List Pt) (m : Macro) (b : Quad) :
    macroLB pts m b = SigmaQuarter.macroLB pts m b := by
  simp only [macroLB,SigmaQuarter.macroLB,sigSum_eq]

def axisOK (pts : List Pt) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b =>
    decide (QuarterCompute.FastAxisNode.axisGeom b) &&
    decide ((b.2.2.2.1 : ℚ)/2^32 ≤ QuarterCompute.FastAxisNode.quarterAxisLB (macroLB pts m b.1)
      (QuarterCompute.FastAxisNode.axisUt b.1.1 b.1.2.1)
      (QuarterCompute.FastAxisNode.axisUt b.2.1 b.2.2.1)))

lemma axisOK_eq (pts : List Pt) (m : Macro) : axisOK pts m = SigmaQuarter.axisOK pts m := by
  simp only [axisOK,SigmaQuarter.axisOK,FastAxisNodePure.axisGeom_eq,
    FastAxisNodePure.axisUt_eq,FastAxisNodePure.quarterAxisLB_eq,macroLB_eq]

def rayOK (epsilon : ℚ) (pts : List Pt) (mp : ℚ) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b => decide (QuarterCompute.FastNode.boxGeom b) &&
    decide (mp ≤ QuarterCompute.FastNode.quarterBoxLB epsilon (macroLB pts m b.1)
      b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2))

lemma rayOK_eq (epsilon : ℚ) (pts : List Pt) (mp : ℚ) (m : Macro) :
    rayOK epsilon pts mp m = QuarterContour.rayOK epsilon pts mp m := by
  simp only [rayOK,QuarterContour.rayOK,FastNodePure.boxGeom_eq,
    FastNodePure.quarterBoxLB_eq,QuarterContour.FastNode.quarterBoxLB_eq,macroLB_eq]
end CatalanCore.Cert.QuarterContour.FastMacros
#print axioms CatalanCore.Cert.QuarterContour.FastMacros.farOK_eq
#print axioms CatalanCore.Cert.QuarterContour.FastMacros.axisOK_eq
#print axioms CatalanCore.Cert.QuarterContour.FastMacros.rayOK_eq