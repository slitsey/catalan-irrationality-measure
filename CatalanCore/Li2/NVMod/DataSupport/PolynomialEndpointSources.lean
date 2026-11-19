module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialFamily
public import CatalanCore.Li2.NVMod.EndpointOne
public import CatalanCore.Li2.NVMod.InfinityDefinitions
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

def harmonicSquare (m : ℕ) : ℚ := ((List.range m).map (fun (j : ℕ)=>1/((j+1:ℕ):ℚ)^2)).sum

def regularMomentWith (ms : List ℕ) (rho : ℕ→ℚ) (e : ℕ) : ℚ :=
  (ms.map (fun (m : ℕ)=>rho m*(-(m:ℚ))^e*harmonicSquare m)).sum

theorem regularMomentWith_spec (A : TypeKey) (ms : List ℕ) (rho : ℕ→ℚ)
    (hn : ms.Nodup) (hs : ms.toFinset=poleSet A)
    (hr : ∀ m∈ms.toFinset,rho m=residue A m) (e : ℕ) :
    regularMomentWith ms rho e=regularMoment A e := by
  unfold regularMomentWith
  rw [←List.sum_toFinset (fun m : ℕ=>rho m*(-(m:ℚ))^e*harmonicSquare m) hn]
  unfold regularMoment
  rw [←hs]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hr m hm]
  congr 1
  exact shifted_range_sum (fun j : ℕ=>(1:ℚ)/(j:ℚ)^2) m

theorem zeroLead_with_residues (A : TypeKey) (rho : ℕ→ℚ)
    (hr : ∀ m∈poleSet A,rho m=residue A m) :
    zeroLead A=((topPoles A).map rho).prod*diffProduct (topPoles A) := by
  unfold zeroLead
  congr 2
  apply List.map_congr_left
  intro m hm
  have hp : m∈positivePoles A:=List.mem_reverse.mp (List.mem_of_mem_take hm)
  exact (hr m ((mem_positivePoles A m).mp hp).2).symm

def oneLeadWith (h : ℤ) (size : ℕ) (v : ℕ→ℚ) : Option ℚ :=
  let h1:=((h+1)/2).toNat
  if h<0 then some (∏ k : Fin size,(k.val.factorial:ℚ)*((k.val+h.natAbs).factorial:ℚ))
  else if Odd h then
    if size≤h1 then ratDet size (Matrix.of fun i j : Fin size=>v (i.val+j.val))
    else (ratDet h1 (Matrix.of fun i j : Fin h1=>v (i.val+j.val))).map
      (fun q=>q*∏ k : Fin (size-h1),(k.val.factorial:ℚ)*((k.val+1).factorial:ℚ))
  else if size≤h1+1 then ratDet size (Matrix.of fun i j : Fin size=>v (i.val+j.val))
  else (ratDet (h1+1) (Matrix.of fun i j : Fin (h1+1)=>v (i.val+j.val)-
      if i.val=h1 ∧ j.val=h1 then ((size-h1-1:ℕ):ℚ)/((size-h1-1:ℕ)+1) else 0)).map
    (fun q=>q*∏ k : Fin (size-h1-1),(k.val.factorial:ℚ)*((k.val+2).factorial:ℚ))

theorem oneLeadWith_spec (A : TypeKey) (h : ℤ) (v : ℕ→ℚ)
    (hh : h0 A=h) (hv : ∀ e,v e=regularMoment A e) :
    oneLead A=oneLeadWith h A.size v := by
  subst h
  have hmat (n : ℕ) : regularHankel A n=Matrix.of (fun i j : Fin n=>v (i.val+j.val)) := by
    apply Matrix.ext
    intro i j
    exact (hv _).symm
  have hc : cornerHankel A=Matrix.of (fun i j : Fin (oneH1 A+1)=>v (i.val+j.val)-
      if i.val=oneH1 A ∧ j.val=oneH1 A then
        ((A.size-oneH1 A-1:ℕ):ℚ)/((A.size-oneH1 A-1:ℕ)+1) else 0) := by
    apply Matrix.ext
    intro i j
    change regularMoment A (i.val+j.val)-_=v (i.val+j.val)-_
    rw [hv]
  simp only [oneLead,oneLeadWith,hmat,hc,oneH1]

def earlierValue (kind : Kind) (ts : List ℕ) (t : ℕ) : ℚ :=
  (if kind=.U then -(t:ℚ) else 1)*(ts.map (fun (u : ℕ)=>((u:ℚ)-t)^3)).prod

theorem earlierValue_spec (A : TypeKey) (ts : List ℕ) (t : ℕ) :
    (earlierPoly A ts).eval (-(t:ℚ))=earlierValue A.kind ts t := by
  induction ts with
  | nil=>cases hk : A.kind <;> simp [earlierPoly,earlierValue,hk]
  | cons u us ih=>
    have hs : earlierPoly A (u::us)=(X+C (u:ℚ))^3*earlierPoly A us := by
      cases hk : A.kind <;> simp [earlierPoly,hk] <;> ring
    rw [hs,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C,ih]
    simp only [earlierValue,List.map_cons,List.prod_cons,sub_eq_add_neg]
    ring

def infFoldWith (A : TypeKey) (rho : ℕ→ℚ) : List ℕ→ℕ→List ℕ→ℚ
  | [],_,_=>1
  | t::ts,left,earlier=>
    if left=0 then 1 else if 3≤left then
      (rho t)^3*(earlierValue A.kind earlier t)^6*infFoldWith A rho ts (left-3) (earlier++[t])
    else partialInf A earlier t left

theorem infFoldWith_spec (A : TypeKey) (rho : ℕ→ℚ) (ts : List ℕ)
    (hr : ∀ t∈ts,rho t=residue A t) (left : ℕ) (earlier : List ℕ) :
    infFold A ts left earlier=infFoldWith A rho ts left earlier := by
  induction ts generalizing left earlier with
  | nil=>rfl
  | cons t ts ih=>
    simp only [infFold,infFoldWith]
    split_ifs
    · rfl
    · rw [←hr t (by simp),earlierValue_spec,ih (fun u hu=>hr u (by simp [hu]))]
    · rfl

def infLeadWith (A : TypeKey) (rho : ℕ→ℚ) : ℚ :=
  if A.size=0 then 1 else
  if A.kind=.U then -rfEval (rfDeriv (weight A)) 0*infFoldWith A rho (poleList A) (A.size-1) []
  else infFoldWith A rho (poleList A) A.size []

theorem infLeadWith_spec (A : TypeKey) (rho : ℕ→ℚ)
    (hr : ∀ m∈poleSet A,rho m=residue A m) : infLead A=infLeadWith A rho := by
  have hh := infFoldWith_spec A rho (poleList A) (fun m hm=>hr m ((mem_poleList A m).mp hm))
  unfold infLead infLeadWith
  split_ifs <;> simp only [hh]
#print axioms regularMomentWith_spec
#print axioms zeroLead_with_residues
#print axioms oneLeadWith_spec
#print axioms infLeadWith_spec
end
end CatalanCore.Li2.NVMod.DataSupport
