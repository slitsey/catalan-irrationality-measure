module
public import CatalanCore.Cert.QuarterContour.FastMacros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ScalarFar
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

/- Each recursive result is a single integer. No recursive FD or FD projection occurs. -/
def sumL (x0 y0 : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*QuarterCompute.FastNode.logUp (SigmaP6.farQ x0 y0 p)+sumL x0 y0 ps

def sumAx (x0 y0 : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*(x0-p.1)*(SigmaP6.farLo x0 y0 p : ℤ)+sumAx x0 y0 ps

def sumEx (x0 y0 : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*((x0-p.1).natAbs : ℤ)+sumEx x0 y0 ps

def sumAy (x0 y0 : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*(y0-p.2.1)*(SigmaP6.farLo x0 y0 p : ℤ)+sumAy x0 y0 ps

def sumEy (x0 y0 : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*((y0-p.2.1).natAbs : ℤ)+sumEy x0 y0 ps

def sumH (x0 y0 : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*((SigmaP6.farLo x0 y0 p : ℤ)+1)+sumH x0 y0 ps

lemma reconstruct (x0 y0 : ℤ) (ps : List Pt) :
    (sumL x0 y0 ps,sumAx x0 y0 ps,sumEx x0 y0 ps,
      sumAy x0 y0 ps,sumEy x0 y0 ps,sumH x0 y0 ps) = FastMacros.farSum x0 y0 ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [FastMacros.farSum,←ih]
    rfl

lemma farOK_of_components (pts : List Pt) (m : Macro)
    (hL : sumL m.x0 m.y0 (macroFar pts m) = m.fd.1)
    (hAx : sumAx m.x0 m.y0 (macroFar pts m) = m.fd.2.1)
    (hEx : sumEx m.x0 m.y0 (macroFar pts m) = m.fd.2.2.1)
    (hAy : sumAy m.x0 m.y0 (macroFar pts m) = m.fd.2.2.2.1)
    (hEy : sumEy m.x0 m.y0 (macroFar pts m) = m.fd.2.2.2.2.1)
    (hH : sumH m.x0 m.y0 (macroFar pts m) = m.fd.2.2.2.2.2) :
    SigmaQuarter.farOK pts m := by
  unfold SigmaQuarter.farOK
  rw [←FastMacros.farSum_eq,←reconstruct,hL,hAx,hEx,hAy,hEy,hH]

example : sumL 0 0 [] = 0 := rfl
example : sumAx 3 5 [(1,2,7)] = 7*2*(SigmaP6.farLo 3 5 (1,2,7) : ℤ) := rfl
example : sumEy 3 5 [(1,7,2),(4,4,3)] = 7 := rfl
end CatalanCore.Cert.QuarterContour.ScalarFar
#print axioms CatalanCore.Cert.QuarterContour.ScalarFar.reconstruct
#print axioms CatalanCore.Cert.QuarterContour.ScalarFar.farOK_of_components
