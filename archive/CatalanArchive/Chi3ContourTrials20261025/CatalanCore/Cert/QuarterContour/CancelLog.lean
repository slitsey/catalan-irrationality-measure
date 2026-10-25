module
public import CatalanCore.Cert.QuarterContour.FastMacros
public import Mathlib.Algebra.Order.Floor.Div
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.CancelLog
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

/-- Cancelling a common positive factor preserves the ceiling quotient, even at denominator zero. -/
lemma ceil_scale (a b q : ℕ) (hq : 0 < q) :
    (a*q+b*q-1)/(b*q) = (a+b-1)/b := by
  by_cases hb : b = 0
  · simp [hb]
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  change (a*q) ⌈/⌉ (b*q) = a ⌈/⌉ b
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul (Nat.mul_pos hbpos hq)).2
    have ha : a ≤ b*(a ⌈/⌉ b) := (ceilDiv_le_iff_le_mul hbpos).mp le_rfl
    have h := Nat.mul_le_mul_right q ha
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
  · apply (ceilDiv_le_iff_le_mul hbpos).2
    have h : a*q ≤ (b*q)*((a*q) ⌈/⌉ (b*q)) := (ceilDiv_le_iff_le_mul (Nat.mul_pos hbpos hq)).mp le_rfl
    apply Nat.le_of_mul_le_mul_right (c := q) _ hq
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

/-- The actual upper-log correction with its shared power of two removed before division. -/
def correction (N m L : ℕ) : ℕ :=
  let k := min L 72
  (N*2^(72-k)+m*2^(L-k)-1)/(m*2^(L-k))

lemma correction_eq (N m L : ℕ) :
    correction N m L = (N*2^72+m*2^L-1)/(m*2^L) := by
  let k := min L 72
  have h72 : 72-k+k = 72 := Nat.sub_add_cancel (Nat.min_le_right L 72)
  have hL : L-k+k = L := Nat.sub_add_cancel (Nat.min_le_left L 72)
  have h := (ceil_scale (N*2^(72-k)) (m*2^(L-k)) (2^k) (by positivity)).symm
  change (N*2^(72-k)+m*2^(L-k)-1)/(m*2^(L-k)) = _
  simpa only [Nat.mul_assoc,←Nat.pow_add,h72,hL] using h

def logUp (N : ℕ) : ℤ :=
  let L := Nat.log2 N
  let m := N*2^8/2^L
  let e : ℤ := ((L : ℤ)-80)*(if 80 ≤ L then (QuarterCompute.FastTableData.up 256 : ℤ) else (QuarterCompute.FastTableData.lo 256 : ℤ))
  let c : ℤ := correction N m L
  e+(QuarterCompute.FastTableData.up (m-256) : ℤ)+c-2^64

lemma fastLogUp_eq (N : ℕ) : logUp N = QuarterCompute.FastNode.logUp N := by
  simp only [logUp,QuarterCompute.FastNode.logUp,correction_eq]

def sigSum (xl xh yl yh : ℤ) : List Pt → ℤ
  | [] => 0
  | p::ps => (p.2.2 : ℤ)*logUp (SigmaP6.qplusN xl xh yl yh p)+sigSum xl xh yl yh ps

lemma sigSum_eq (xl xh yl yh : ℤ) (ps : List Pt) :
    sigSum xl xh yl yh ps = FastMacros.sigSum xl xh yl yh ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [sigSum,FastMacros.sigSum,fastLogUp_eq,ih]

def farTerm (x0 y0 : ℤ) (p : Pt) : FD :=
  ((p.2.2 : ℤ)*logUp (SigmaP6.farQ x0 y0 p),
   (p.2.2 : ℤ)*(x0-p.1)*(SigmaP6.farLo x0 y0 p : ℤ),
   (p.2.2 : ℤ)*((x0-p.1).natAbs : ℤ),
   (p.2.2 : ℤ)*(y0-p.2.1)*(SigmaP6.farLo x0 y0 p : ℤ),
   (p.2.2 : ℤ)*((y0-p.2.1).natAbs : ℤ),
   (p.2.2 : ℤ)*((SigmaP6.farLo x0 y0 p : ℤ)+1))

lemma farTerm_eq (x0 y0 : ℤ) (p : Pt) : farTerm x0 y0 p = FastMacros.farTerm x0 y0 p := by
  simp only [farTerm,FastMacros.farTerm,fastLogUp_eq]

def farSum (x0 y0 : ℤ) : List Pt → FD
  | [] => (0,0,0,0,0,0)
  | p::ps => SigmaP6.fdAdd (farTerm x0 y0 p) (farSum x0 y0 ps)

lemma farSum_eq (x0 y0 : ℤ) (ps : List Pt) : farSum x0 y0 ps = FastMacros.farSum x0 y0 ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [farSum,FastMacros.farSum,farTerm_eq,ih]

def farOK (pts : List Pt) (m : Macro) : Prop := farSum m.x0 m.y0 (macroFar pts m) = m.fd
instance (pts : List Pt) (m : Macro) : Decidable (farOK pts m) := by unfold farOK;infer_instance
lemma farOK_eq (pts : List Pt) (m : Macro) : farOK pts m = SigmaQuarter.farOK pts m := by
  simp only [farOK,SigmaQuarter.farOK,farSum_eq,FastMacros.farSum_eq]

def macroLB (pts : List Pt) (m : Macro) (b : Quad) : ℚ :=
  SigmaP6.sigTL m.x0 m.y0 m.fd b.1 b.2.1 b.2.2.1 b.2.2.2
    (sigSum b.1 b.2.1 b.2.2.1 b.2.2.2 (macroNear pts m))
lemma macroLB_eq (pts : List Pt) (m : Macro) (b : Quad) : macroLB pts m b = FastMacros.macroLB pts m b := by
  simp only [macroLB,FastMacros.macroLB,sigSum_eq]

def rayOK (epsilon : ℚ) (pts : List Pt) (mp : ℚ) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b => decide (QuarterCompute.FastNode.boxGeom b) &&
    decide (mp ≤ QuarterCompute.FastNode.quarterBoxLB epsilon (macroLB pts m b.1)
      b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2))
lemma rayOK_eq (epsilon : ℚ) (pts : List Pt) (mp : ℚ) (m : Macro) :
    rayOK epsilon pts mp m = QuarterContour.rayOK epsilon pts mp m := by
  rw [←FastMacros.rayOK_eq]
  simp only [rayOK,FastMacros.rayOK,macroLB_eq]

example : correction 0 0 0 = 0 := rfl
example : correction 7 0 80 = 0 := rfl
example : correction 7 3 0 = (7*2^72+3-1)/3 := rfl
end CatalanCore.Cert.QuarterContour.CancelLog
#print axioms CatalanCore.Cert.QuarterContour.CancelLog.correction_eq
#print axioms CatalanCore.Cert.QuarterContour.CancelLog.fastLogUp_eq
#print axioms CatalanCore.Cert.QuarterContour.CancelLog.farOK_eq
#print axioms CatalanCore.Cert.QuarterContour.CancelLog.rayOK_eq
