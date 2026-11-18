module
public import CatalanCore.Li2.NVMod.ResInv
public import CatalanCore.Linalg.HankelRecurrence
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2.NVMod

def subNat (p a b : ℕ) : ℕ := (a+p-b%p)%p
theorem subNat_cast (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    (subNat p a b:ZMod p)=(a:ZMod p)-(b:ZMod p) := by
  have hb : b%p≤a+p := by have hh:=Nat.mod_lt b (Fact.out : p.Prime).pos;omega
  simp only [subNat,ZMod.natCast_mod,Nat.cast_sub hb,Nat.cast_add,ZMod.natCast_self,add_zero]

theorem cast_getD (p : ℕ) (xs : List ℕ) (j : ℕ) :
    (xs.map (fun n : ℕ=>(n:ZMod p))).getD j 0=(xs.getD j 0:ZMod p) := by
  simpa only [Nat.cast_zero] using List.getD_map xs 0 (n:=j) (fun n : ℕ=>(n:ZMod p))
theorem nat_mod_ne_zero_iff (p x : ℕ) : x%p≠0 ↔ (x:ZMod p)≠0 := by
  simp only [ne_eq,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]

def djLoopNat (p : ℕ) (C : PrimeInverseTable) : ℕ→List ℕ→List ℕ→Option ℕ
  | 0,_,cur=>cur.head?
  | fuel+1,prev,cur=>
    if prev.length=cur.length+2 ∧ 3≤cur.length ∧
        (List.range (cur.length-2)).all (fun j=>decide (prev.getD (j+2) 0%p≠0)) then
      let next := (List.range (cur.length-2)).map (fun j=>
        (subNat p (cur.getD j 0*cur.getD (j+2) 0) (cur.getD (j+1) 0^2)*
          inverseNat p C (prev.getD (j+2) 0))%p)
      djLoopNat p C fuel cur next
    else none
def djEvalNat (p : ℕ) (C : PrimeInverseTable) (n : ℕ) (m : List ℕ) : Option ℕ :=
  if n=0 then some 1 else
    if m.length=2*n-1 then djLoopNat p C (n-1) (List.replicate (2*n+1) 1) m else none

theorem djLoopNat_cast (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (fuel : ℕ) (prev cur : List ℕ) :
    (djLoopNat p C fuel prev cur).map (fun n : ℕ=>(n:ZMod p))=
      CatalanCore.Linalg.djLoop fuel (prev.map (fun n : ℕ=>(n:ZMod p))) (cur.map (fun n : ℕ=>(n:ZMod p))) := by
  induction fuel generalizing prev cur with
  | zero => cases cur <;> rfl
  | succ fuel ih =>
    have hguard :
        (prev.length=cur.length+2 ∧ 3≤cur.length ∧
          (List.range (cur.length-2)).all (fun j=>decide (prev.getD (j+2) 0%p≠0))) ↔
        ((prev.map (fun n : ℕ=>(n:ZMod p))).length=(cur.map (fun n : ℕ=>(n:ZMod p))).length+2 ∧
          3≤(cur.map (fun n : ℕ=>(n:ZMod p))).length ∧
          (List.range ((cur.map (fun n : ℕ=>(n:ZMod p))).length-2)).all (fun j=>
            decide ((prev.map (fun n : ℕ=>(n:ZMod p))).getD (j+2) 0≠0))) := by
      simp only [List.length_map,cast_getD,nat_mod_ne_zero_iff]
    by_cases hg : prev.length=cur.length+2 ∧ 3≤cur.length ∧
        (List.range (cur.length-2)).all (fun j=>decide (prev.getD (j+2) 0%p≠0))
    · rw [djLoopNat,if_pos hg,CatalanCore.Linalg.djLoop,if_pos (hguard.mp hg)]
      rw [ih]
      congr 1
      simp only [List.length_map,List.map_map]
      apply congrArg (fun f : ℕ→ZMod p=>(List.range (cur.length-2)).map f)
      funext j
      simp only [Function.comp_apply,ZMod.natCast_mod,Nat.cast_mul,subNat_cast,Nat.cast_pow,
        (inverseNat_sound p C hC _).2,cast_getD,div_eq_mul_inv]
    · rw [djLoopNat,if_neg hg,CatalanCore.Linalg.djLoop,if_neg (fun h=>hg (hguard.mpr h))]
      rfl

theorem djEvalNat_cast (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) :
    (djEvalNat p C n m).map (fun x : ℕ=>(x:ZMod p))=
      CatalanCore.Linalg.djEval n (m.map (fun x : ℕ=>(x:ZMod p))) := by
  by_cases hn : n=0
  · simp [djEvalNat,CatalanCore.Linalg.djEval,hn]
  · by_cases hm : m.length=2*n-1
    · simp only [djEvalNat,CatalanCore.Linalg.djEval,if_neg hn,List.length_map,if_pos hm]
      simpa only [List.map_replicate,Nat.cast_one] using
        djLoopNat_cast p C hC (n-1) (List.replicate (2*n+1) 1) m
    · simp only [djEvalNat,CatalanCore.Linalg.djEval,if_neg hn,List.length_map,if_neg hm,Option.map_none]

theorem djEvalNat_sound (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) (v : ℕ)
    (h : djEvalNat p C n m=some v) :
    (v:ZMod p)=(CatalanCore.Linalg.hankel (m.map (fun x : ℕ=>(x:ZMod p))) n 0).det := by
  have hc := djEvalNat_cast p C hC n m
  rw [h,Option.map_some] at hc
  exact CatalanCore.Linalg.djEval_sound n _ _ hc.symm

theorem djEvalNat_scalar (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) (v : ℕ)
    (h : djEvalNat p C n m=some v) :
    CatalanCore.Linalg.scalarEval n (m.map (fun x : ℕ=>(x:ZMod p)))=some (v:ZMod p) := by
  have hc := djEvalNat_cast p C hC n m
  rw [h,Option.map_some] at hc
  rw [CatalanCore.Linalg.scalarEval,←hc]

#print axioms djLoopNat_cast
#print axioms djEvalNat_sound
#print axioms djEvalNat_scalar
end CatalanCore.Li2.NVMod

