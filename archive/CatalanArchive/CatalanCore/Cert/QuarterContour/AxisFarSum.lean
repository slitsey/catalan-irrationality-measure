module
public import CatalanCore.Cert.QuarterContour.AxisSigSum
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.AxisFarSum
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

lemma farQ_pair (x0 : ℤ) (p q : Pt) (hx : p.1 = q.1) (hy : p.2.1 = -q.2.1) :
    SigmaP6.farQ x0 0 p = SigmaP6.farQ x0 0 q := by
  simp only [SigmaP6.farQ,zero_sub,Int.natAbs_neg,hx,hy]

/-- The vertical gradient retains the signed mass difference; the other fields use the sum. -/
def pairTerm (x0 : ℤ) (p q : Pt) : FD :=
  let mass := (p.2.2 : ℤ)+(q.2.2 : ℤ)
  let diff := (p.2.2 : ℤ)-(q.2.2 : ℤ)
  let Q := SigmaP6.farQ x0 0 p
  let lo : ℤ := ((2^100/Q : ℕ) : ℤ)
  (mass*QuarterCompute.FastNode.logUp Q,
   mass*(x0-p.1)*lo,
   mass*((x0-p.1).natAbs : ℤ),
   diff*(0-p.2.1)*lo,
   mass*((0-p.2.1).natAbs : ℤ),
   mass*(lo+1))

lemma pairTerm_eq (x0 : ℤ) (p q : Pt) (hx : p.1 = q.1) (hy : p.2.1 = -q.2.1) :
    pairTerm x0 p q = SigmaP6.fdAdd (FastMacros.farTerm x0 0 p) (FastMacros.farTerm x0 0 q) := by
  have hQ : SigmaP6.farQ x0 0 q = SigmaP6.farQ x0 0 p := (farQ_pair x0 p q hx hy).symm
  have hX : q.1 = p.1 := hx.symm
  have hY : q.2.1 = -p.2.1 := by omega
  simp only [pairTerm,FastMacros.farTerm,SigmaP6.fdAdd,SigmaP6.farLo,
    hQ,hX,hY,zero_sub,neg_neg,Int.natAbs_neg]
  ext <;> ring

lemma fdAdd_assoc (a b c : FD) :
    SigmaP6.fdAdd (SigmaP6.fdAdd a b) c = SigmaP6.fdAdd a (SigmaP6.fdAdd b c) := by
  simp only [SigmaP6.fdAdd,add_assoc]

def axisSum (x0 : ℤ) : List Pt → FD
  | [] => (0,0,0,0,0,0)
  | [p] => FastMacros.farSum x0 0 [p]
  | p::q::ps =>
    if AxisSigSum.paired p q then SigmaP6.fdAdd (pairTerm x0 p q) (axisSum x0 ps)
    else SigmaP6.fdAdd (FastMacros.farTerm x0 0 p) (axisSum x0 (q::ps))

lemma axisSum_eq (x0 : ℤ) (ps : List Pt) : axisSum x0 ps = FastMacros.farSum x0 0 ps := by
  induction ps using List.twoStepInduction with
  | nil => rfl
  | singleton p => rfl
  | cons_cons p q ps ih0 ih1 =>
    rw [axisSum]
    split_ifs with h
    · have hp : p.1 = q.1 ∧ p.2.1 = -q.2.1 := of_decide_eq_true h
      rw [ih0,pairTerm_eq x0 p q hp.1 hp.2,fdAdd_assoc]
      rfl
    · rw [ih1 q]
      rfl

/-- Other centre heights retain the accepted evaluator verbatim. -/
def farSum (x0 y0 : ℤ) (ps : List Pt) : FD :=
  if y0 = 0 then axisSum x0 ps else FastMacros.farSum x0 y0 ps

lemma farSum_eq (x0 y0 : ℤ) (ps : List Pt) : farSum x0 y0 ps = FastMacros.farSum x0 y0 ps := by
  unfold farSum
  split_ifs with h
  · subst y0;exact axisSum_eq x0 ps
  · rfl

def farOK (pts : List Pt) (m : Macro) : Prop := farSum m.x0 m.y0 (macroFar pts m) = m.fd
instance (pts : List Pt) (m : Macro) : Decidable (farOK pts m) := by unfold farOK;infer_instance

lemma farOK_eq_fast (pts : List Pt) (m : Macro) : farOK pts m = FastMacros.farOK pts m := by
  simp only [farOK,FastMacros.farOK,farSum_eq]

lemma farOK_eq (pts : List Pt) (m : Macro) : farOK pts m = SigmaQuarter.farOK pts m :=
  (farOK_eq_fast pts m).trans (FastMacros.farOK_eq pts m)
end CatalanCore.Cert.QuarterContour.AxisFarSum
#print axioms CatalanCore.Cert.QuarterContour.AxisFarSum.pairTerm_eq
#print axioms CatalanCore.Cert.QuarterContour.AxisFarSum.farOK_eq