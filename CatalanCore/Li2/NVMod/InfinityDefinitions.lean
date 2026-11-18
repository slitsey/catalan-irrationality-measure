module
public import CatalanCore.Li2.NVMod.RationalRules
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
def poleList (A : TypeKey) : List ℕ :=
  (List.range (A.c+1)).filter (fun m=>m∈poleSet A)
def slots (A : TypeKey) : List ℕ :=
  (if A.kind=.U then [0] else [])++(poleList A).flatMap (fun m=>[m,m,m])
def infOrder (A : TypeKey) : ℤ :=
  (((slots A).take A.size).map (fun m=>(m:ℤ))).sum
def earlierPoly (A : TypeKey) (ts : List ℕ) : ℚ[X] :=
  (if A.kind=.U then X else 1)*(ts.map (fun t=>(X+C (t:ℚ))^3)).prod
def partialInf (A : TypeKey) (ts : List ℕ) (t take : ℕ) : ℚ :=
  let Q := earlierPoly A ts
  let Φ := (rfX+rfPoly (C (t:ℚ)))*(rfPoly Q)^2*weight A
  let v := rfEval Φ (-(t:ℚ))
  let σ := rfEval (rfDeriv Φ/Φ) (-(t:ℚ))
  let σ' := rfEval (rfDeriv (rfDeriv Φ/Φ)) (-(t:ℚ))
  if take=1 then -v*(σ^2+σ')/2 else v^2*(σ'-σ^2)/2
def infFold (A : TypeKey) : List ℕ→ℕ→List ℕ→ℚ
  | [],_,_=>1
  | t::ts,left,earlier=>
    if left=0 then 1 else if 3≤left then
      (residue A t)^3*((earlierPoly A earlier).eval (-(t:ℚ)))^6*
        infFold A ts (left-3) (earlier++[t])
    else partialInf A earlier t left
def infLead (A : TypeKey) : ℚ :=
  if A.size=0 then 1 else
  if A.kind=.U then -rfEval (rfDeriv (weight A)) 0*infFold A (poleList A) (A.size-1) []
  else infFold A (poleList A) A.size []
theorem mem_poleList (A : TypeKey) (m : ℕ) : m∈poleList A↔m∈poleSet A := by
  simp only [poleList,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · exact fun h=>h.2
  · intro hm
    refine ⟨?_,hm⟩
    cases hk : A.kind <;> simp only [poleSet,hk,Finset.mem_Ico,Finset.mem_Ioc] at hm <;> omega
theorem poleList_nodup (A : TypeKey) : (poleList A).Nodup := List.nodup_range.filter _
theorem poleList_pairwise (A : TypeKey) : (poleList A).Pairwise (·<·) := List.pairwise_lt_range.filter _
theorem poleList_U_pos (A : TypeKey) (hU : A.kind=.U) (m : ℕ) (hm : m∈poleList A) : 1≤m := by
  rw [mem_poleList] at hm
  simp only [poleSet,hU,Finset.mem_Ioc] at hm
  omega
theorem slots_length (A : TypeKey) :
    (slots A).length=(if A.kind=.U then 1 else 0)+3*(poleList A).length := by
  have hlen (ts : List ℕ) : (ts.flatMap (fun m=>[m,m,m])).length=3*ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih => simp [ih,Nat.mul_add,Nat.add_assoc]
  unfold slots
  rw [List.length_append,hlen]
  split_ifs <;> rfl
theorem earlierPoly_monic (A : TypeKey) (ts : List ℕ) : (earlierPoly A ts).Monic := by
  have hp : ((ts.map (fun t=>(X+C (t:ℚ))^3)).prod).Monic := by
    induction ts with
    | nil => simpa using Polynomial.monic_one (R:=ℚ)
    | cons t ts ih =>
      change (((X+C (t:ℚ))^3)*(ts.map (fun t=>(X+C (t:ℚ))^3)).prod).Monic
      exact ((Polynomial.monic_X_add_C _).pow 3).mul ih
  unfold earlierPoly
  apply Polynomial.Monic.mul _ hp
  split_ifs
  · exact Polynomial.monic_X
  · exact Polynomial.monic_one
theorem earlierPoly_eval_ne_zero (A : TypeKey) (ts : List ℕ) (t : ℕ)
    (ht : t∉ts) (hU : A.kind=.U→t≠0) : (earlierPoly A ts).eval (-(t:ℚ))≠0 := by
  have hp : ((ts.map (fun m=>(X+C (m:ℚ))^3)).prod).eval (-(t:ℚ))≠0 := by
    induction ts with
    | nil => simp
    | cons m ms ih =>
      have hm : m≠t := by intro he;apply ht;simp [he]
      have hn : (m:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hm)
      change (((X+C (m:ℚ))^3)*(ms.map (fun m=>(X+C (m:ℚ))^3)).prod).eval (-(t:ℚ))≠0
      simp only [Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
      apply mul_ne_zero (pow_ne_zero 3 (by simpa only [sub_eq_add_neg,add_comm] using hn))
      exact ih (fun h=>ht (List.mem_cons_of_mem m h))
  rw [earlierPoly,Polynomial.eval_mul]
  apply mul_ne_zero _ hp
  split_ifs with h
  · simpa only [Polynomial.eval_X,neg_ne_zero,Nat.cast_ne_zero] using hU h
  · simp
#print axioms mem_poleList
#print axioms poleList_pairwise
#print axioms slots_length
#print axioms earlierPoly_monic
#print axioms earlierPoly_eval_ne_zero
end
end CatalanCore.Li2.NVMod
