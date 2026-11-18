module
public import CatalanCore.Li2.DecayCert.Seg.NodeDefs
public import CatalanCore.Li2.DecayCert.Seg.NodeCells
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists
/-! Kernel-computable twins of the polynomial checks in the decay data (source densities and atom
caps), for any frame: each twin works on coefficient lists and is proved to imply (or equal) the
`ℚ[X]` check. `nodeSegmentCheck_of_fast` assembles the node check from the twins and the rest. -/
@[expose] public section
set_option Elab.async false
open Polynomial Set
namespace CatalanCore.Li2.DecayCert
open LatticeGate
noncomputable section

/-- Equality of the polynomials of two coefficient lists (trailing zeros ignored). -/
def qListEq (a b : List ℚ) : Bool :=
  (List.range (max a.length b.length)).all (fun j : ℕ => decide (coeffQ a j=coeffQ b j))

theorem qListPoly_eq_of (a b : List ℚ) (h : qListEq a b=true) : qListPoly a=qListPoly b := by
  ext j
  rw [qListPoly_coeff,qListPoly_coeff]
  by_cases hj : j < max a.length b.length
  · exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr hj))
  · rw [coeffQ_eq_zero_of_ge a j (by omega),coeffQ_eq_zero_of_ge b j (by omega)]

def qListMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c::a, b => qListAdd (qListScale c b) (qListShift (qListMul a b))

theorem qListPoly_nil : qListPoly []=0 := by simp [qListPoly]

theorem qListPoly_cons (c : ℚ) (a : List ℚ) : qListPoly (c::a)=C c+X*qListPoly a := by
  ext j
  cases j with
  | zero => simp [qListPoly_coeff,coeffQ]
  | succ j =>
    rw [Polynomial.coeff_add,Polynomial.coeff_X_mul,qListPoly_coeff,qListPoly_coeff,Polynomial.coeff_C]
    simp [coeffQ]

theorem qListPoly_mul (a b : List ℚ) : qListPoly (qListMul a b)=qListPoly a*qListPoly b := by
  induction a with
  | nil => simp [qListMul,qListPoly_nil]
  | cons c a ih =>
    rw [qListMul,qListPoly_add,qListPoly_scale,qListPoly_shift,ih,qListPoly_cons]
    ring

/-- `sourceDataCheck` on coefficient lists. -/
def sourceDataCheckFast (segments : List QSegment) (radius : ℚ) (w : DensityWitness) : Bool :=
  decide (0 ≤ radius ∧ segments.length=w.trees.length ∧ (segments.map (fun s => s.c 0)).sum=2) &&
    ((List.range segments.length).all (fun j => match segments[j]?,w.trees[j]? with
      | some s,some t => decide (cqSq s.half ≠ 0 ∧ 0 < s.coeff.length ∧
          cqSq (cqAdd s.mid s.half) ≤ radius^2 ∧ cqSq (cqSub s.mid s.half) ≤ radius^2) &&
            bernListCheck (qDensityCoeffs s) (-1) 1 t
      | _,_ => false))

theorem sourceDataCheckFast_eq (segments : List QSegment) (radius : ℚ) (w : DensityWitness) :
    sourceDataCheckFast segments radius w=sourceDataCheck segments radius w := by
  unfold sourceDataCheckFast sourceDataCheck
  congr 1
  congr 1
  funext j
  cases segments[j]? <;> cases w.trees[j]? <;> simp [bernListCheck_eq,qDensityCoeffs_spec]

/-- An atom cap witness from the coefficient list of `g`. -/
noncomputable def capOf (r : List ℚ×BernsteinTree×BernsteinTree×ℚ) : AtomCapWitness :=
  ⟨qListPoly r.1,r.2.1,r.2.2.1,r.2.2.2,8⟩

def capRowCheck (s : QSegment) (r : List ℚ×BernsteinTree×BernsteinTree×ℚ) : Bool :=
  decide (s.mid.2=0 ∧ s.half.2=0 ∧ s.half.1 ≠ 0 ∧ 0 ≤ r.2.2.2) &&
    qListEq (qDensityCoeffs s) (qListMul [1,0,-1] r.1) &&
    bernListCheck r.1 (-1) 1 r.2.1 &&
    bernListCheck (qListSub [r.2.2.2^2] (qListMul [1,0,-1] (qListMul r.1 r.1))) (-1) 1 r.2.2.1 &&
    scalarLowerCheck r.2.2.2 (seScale |s.half.1| .pi)

theorem qListPoly_oneSubSq : qListPoly [1,0,-1]=1-X^2 := by
  simp only [qListPoly_cons,qListPoly_nil]
  simp
  ring

theorem capRowCheck_sound (s : QSegment) (r : List ℚ×BernsteinTree×BernsteinTree×ℚ)
    (h : capRowCheck s r=true) : atomCapCheck s (capOf r)=true := by
  simp only [capRowCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩ := h
  have hden : s.density=(1-X^2)*qListPoly r.1 := by
    rw [← qDensityCoeffs_spec,qListPoly_eq_of _ _ h2,qListPoly_mul,qListPoly_oneSubSq]
  have hb1 : bernCheck (qListPoly r.1) (-1) 1 r.2.1=true := by rw [← bernListCheck_eq]; exact h3
  have e : qListPoly (qListSub [r.2.2.2^2] (qListMul [1,0,-1] (qListMul r.1 r.1)))=
      C (r.2.2.2^2)-(1-X^2)*qListPoly r.1^2 := by
    rw [qListPoly_sub,qListPoly_mul,qListPoly_mul,qListPoly_oneSubSq,qListPoly_cons,qListPoly_nil]
    ring
  have hb2 : bernCheck (C (r.2.2.2^2)-(1-X^2)*qListPoly r.1^2) (-1) 1 r.2.2.1=true := by
    rw [← e,← bernListCheck_eq]; exact h4
  unfold atomCapCheck capOf
  simp only [hb1,hb2,h5,Bool.and_true]
  exact decide_eq_true ⟨h1.1,h1.2.1,h1.2.2.1,h1.2.2.2,hden⟩

def capsCheckFast (atoms : List QSegment) (rows : List (List ℚ×BernsteinTree×BernsteinTree×ℚ)) : Bool :=
  (List.range atoms.length).all (fun j : ℕ => match atoms[j]?,rows[j]? with
    | some a,some r => capRowCheck a r | _,_ => false)

theorem capsCheckFast_sound (atoms : List QSegment) (rows : List (List ℚ×BernsteinTree×BernsteinTree×ℚ))
    (h : capsCheckFast atoms rows=true) :
    ((List.range atoms.length).all (fun j : ℕ => match atoms[j]?,(rows.map capOf)[j]? with
      | some a,some w => atomCapCheck a w | _,_ => false))=true := by
  unfold capsCheckFast at h
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have hj' := h j hj
  simp only [List.getElem?_map]
  cases ha : atoms[j]? <;> cases hr : rows[j]? <;> simp only [ha,hr] at hj' ⊢
  · exact hj'
  · exact hj'
  · exact hj'
  · exact capRowCheck_sound _ _ hj'

namespace Seg
variable {CC AC : Type} [ContourProj CC] [AtomProj AC]

/-- The node check without its two polynomial parts (density and atom caps). -/
def nodeRestCheck (z : ℚ) (b : BentInput) (c : NodeCert CC AC) : Bool :=
  decide (-1 < z ∧ z < 0 ∧ c.atomCaps.length=b.atoms.length) &&
  placementCheck b &&
  nodeContourCoverCheck b c.contour &&
  c.contour.all (fun cell => decide (cell.2.2 ≤ c.ell)) &&
  nodeAtomCoverCheck c.atoms && energyCoverCheck b c.energyCells &&
  scalarUpperCheck (bentTailExpr b c.toBent) c.ell &&
  (match nodeEnergyExpr z b c with | some e => scalarUpperCheck e c.Iup | none => false)

theorem nodeSegmentCheck_of_fast (z : ℚ) (b : BentInput) (c : NodeCert CC AC)
    (rows : List (List ℚ×BernsteinTree×BernsteinTree×ℚ)) (hcaps : c.atomCaps=rows.map capOf)
    (hd : sourceDataCheckFast b.data.segments b.data.radius c.density=true)
    (hc : capsCheckFast b.atoms rows=true) (hr : nodeRestCheck z b c=true) :
    nodeSegmentCheck z b c=true := by
  have hd' : datumCheck b.data c.density=true := by
    rw [datumCheck,← sourceDataCheckFast_eq]; exact hd
  have hc' := capsCheckFast_sound b.atoms rows hc
  rw [← hcaps] at hc'
  simp only [nodeRestCheck,Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩ := hr
  simp only [nodeSegmentCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,hc'⟩,hd'⟩,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩

/-! ### Several shared tables per segment

A segment's shared table fixes `phiHi`, and a copy is admissible only when `phiHi` covers the
cell. One table per segment must then cover the farthest cell, and its majorant inflates every
near cell. So each segment carries a list of tables (checked once), and each cell picks one
table per segment by index. -/

/-- One table per segment, by index into that segment's list. -/
def pickT : List (List SegSharedI) → List ℕ → Option (List SegSharedI)
  | [], [] => some []
  | t::ts, k::ks => match t[k]?, pickT ts ks with
    | some s, some r => some (s::r)
    | _, _ => none
  | _, _ => none

/-- Every table of every segment is valid for its segment. -/
def sharedOKM (S : ℤ) : List QSegment → List (List SegSharedI) → Bool
  | [], [] => true
  | d::ds, t::ts => t.all (fun s => s.ok S d) && sharedOKM S ds ts
  | _, _ => false

theorem pickT_ok (S : ℤ) : ∀ (ds : List QSegment) (tss : List (List SegSharedI)) (sel : List ℕ)
    (ss : List SegSharedI), sharedOKM S ds tss=true → pickT tss sel=some ss → sharedOK S ds ss=true
  | [], [], [], ss, _, h => by simp [pickT] at h; subst h; rfl
  | [], [], _::_, _, _, h => by simp [pickT] at h
  | [], _::_, _, _, h, _ => by simp [sharedOKM] at h
  | _::_, [], _, _, h, _ => by simp [sharedOKM] at h
  | d::ds, t::ts, [], _, _, h => by simp [pickT] at h
  | d::ds, t::ts, k::ks, ss, hm, h => by
    simp only [sharedOKM,Bool.and_eq_true,List.all_eq_true] at hm
    unfold pickT at h
    split at h
    · rename_i s r hs hr
      cases h
      simp only [sharedOK,Bool.and_eq_true]
      exact ⟨hm.1 s (List.mem_of_getElem? hs),pickT_ok S ds ts ks r hm.2 hr⟩
    · cases h

/-- A contour cell checked with its own table selection. -/
noncomputable def contourCellOKM (S G : ℤ) (z : ℚ) (b : BentInput) (tss : List (List SegSharedI))
    (x : ContourCellN×List ℕ) (B : QBox) : Bool :=
  match pickT tss x.2 with
  | some ss => contourCellOK S G z b ss x.1 B
  | none => false

/-- An atom cell checked with its own table selection. -/
noncomputable def atomCellNOKM (S G : ℤ) (z : ℚ) (b : BentInput) (tss : List (List SegSharedI))
    (x : AtomCellN×List ℕ) (o : AtomOut) : Bool :=
  match pickT tss x.2 with
  | some ss => atomCellNOK S G z b ss x.1 o
  | none => false

theorem contourOK_of_M (S G : ℤ) (z : ℚ) (b : BentInput) (tss : List (List SegSharedI))
    (htss : sharedOKM S b.data.segments tss=true) (cs : List ((ContourCellN×List ℕ)×QBox))
    (h : ∀ x ∈ cs,contourCellOKM S G z b tss x.1 x.2=true) :
    ∀ y ∈ cs.map (fun x => (x.1.1,x.2)),∃ ss,sharedOK S b.data.segments ss=true ∧
      contourCellOK S G z b ss y.1 y.2=true := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  have hc := h x hx
  unfold contourCellOKM at hc
  split at hc
  · rename_i ss hp
    exact ⟨ss,pickT_ok S _ tss x.1.2 ss htss hp,hc⟩
  · cases hc

theorem atomOK_of_M (S G : ℤ) (z : ℚ) (b : BentInput) (tss : List (List SegSharedI))
    (htss : sharedOKM S b.data.segments tss=true) (cs : List ((AtomCellN×List ℕ)×AtomOut))
    (h : ∀ x ∈ cs,atomCellNOKM S G z b tss x.1 x.2=true) :
    ∀ y ∈ cs.map (fun x => (x.1.1,x.2)),∃ ss,sharedOK S b.data.segments ss=true ∧
      atomCellNOK S G z b ss y.1 y.2=true := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  have hc := h x hx
  unfold atomCellNOKM at hc
  split at hc
  · rename_i ss hp
    exact ⟨ss,pickT_ok S _ tss x.1.2 ss htss hp,hc⟩
  · cases hc

theorem nodeContourPhysical_of_cellsE (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (cs : List (ContourCellN × QBox))
    (hcs : ∀ x ∈ cs,∃ ss,sharedOK S b.data.segments ss=true ∧ contourCellOK S G z b ss x.1 x.2=true) :
    NodeContourPhysical z b cs := by
  intro x hx
  obtain ⟨ss,hss,hc⟩ := hcs x hx
  exact contourCellOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 hc

theorem nodeAtomPhysical_of_cellsE (S G : ℤ) (hS : 0 < S) (hG : 0 < G) (z : ℚ) (hz : z ≠ 0)
    (b : BentInput) (dw : DensityWitness) (hd : datumCheck b.data dw=true)
    (cs : List (AtomCellN × AtomOut))
    (hcs : ∀ x ∈ cs,∃ ss,sharedOK S b.data.segments ss=true ∧ atomCellNOK S G z b ss x.1 x.2=true) :
    NodeAtomWPhysical z b cs ∧ NodeAtomLinePhysical z b cs := by
  constructor
  · intro x hx
    obtain ⟨ss,hss,hc⟩ := hcs x hx
    exact (atomCellNOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 hc).1
  · intro x hx
    obtain ⟨ss,hss,hc⟩ := hcs x hx
    exact (atomCellNOK_sound S G hS hG z hz b dw hd ss hss x.1 x.2 hc).2

#print axioms nodeSegmentCheck_of_fast
#print axioms contourOK_of_M
#print axioms nodeContourPhysical_of_cellsE
#print axioms nodeAtomPhysical_of_cellsE
end Seg
end
end CatalanCore.Li2.DecayCert
