module
public import CatalanCore.Li2.NVMod.ResCheck
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2.NVMod

def rowCast (p : ℕ) (xs : List ℕ) : List (ZMod p) := xs.map (fun x : ℕ=>(x:ZMod p))
def rowsCast (p : ℕ) (xs : List (List ℕ)) : List (List (ZMod p)) := xs.map (rowCast p)

def pivotRowsNat (p : ℕ) : List (List ℕ)→Option (List ℕ×List (List ℕ)×Bool)
  | []=>none
  | row::rows=>if row.getD 0 0%p≠0 then some (row,rows,false) else
    match pivotRowsNat p rows with
    | none=>none
    | some (a,rs,neg)=>some (a,row::rs,!neg)

def bareissLoopNat (p : ℕ) (C : PrimeInverseTable) : ℕ→ℕ→Bool→List (List ℕ)→Option ℕ
  | 0,_,_,rows=>if rows=[] then some 1 else none
  | 1,_,neg,rows=>match rows with
    | [[x]]=>some (if neg then subNat p 0 x else x%p)
    | _=>none
  | n+2,prev,neg,rows=>
    if rows.length=n+2 ∧ rows.all (fun row=>row.length==n+2) ∧ prev%p≠0 then
      match pivotRowsNat p rows with
      | none=>none
      | some (row,rest,flip)=>
        let pv := row.getD 0 0
        let next := rest.map (fun rr=>List.zipWith (fun a b=>
          (subNat p (pv*a) (rr.getD 0 0*b)*inverseNat p C prev)%p) rr.tail row.tail)
        bareissLoopNat p C (n+1) pv (Bool.xor neg flip) next
    else none

def bareissEvalNat (p : ℕ) (C : PrimeInverseTable) (n : ℕ) (m : List ℕ) : Option ℕ :=
  bareissLoopNat p C n 1 false ((List.range n).map (fun i=>(List.range n).map (fun j=>m.getD (i+j) 0)))

def pivotCast (p : ℕ) (t : List ℕ×List (List ℕ)×Bool) : List (ZMod p)×List (List (ZMod p))×Bool :=
  (rowCast p t.1,rowsCast p t.2.1,t.2.2)

theorem pivotRowsNat_cast (p : ℕ) [Fact p.Prime] (rows : List (List ℕ)) :
    (pivotRowsNat p rows).map (pivotCast p)=CatalanCore.Linalg.pivotRows (rowsCast p rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hiff : row.getD 0 0%p≠0 ↔ (rowCast p row).getD 0 0≠0 := by
      simp only [rowCast,cast_getD,nat_mod_ne_zero_iff]
    by_cases hg : row.getD 0 0%p≠0
    · simp only [pivotRowsNat,rowsCast,List.map_cons,CatalanCore.Linalg.pivotRows,
        if_pos hg,if_pos (hiff.mp hg),Option.map_some,pivotCast]
    · simp only [pivotRowsNat,rowsCast,List.map_cons,CatalanCore.Linalg.pivotRows,
        if_neg hg,if_neg (fun h=>hg (hiff.mpr h))]
      cases hp : pivotRowsNat p rows with
      | none =>
        have hc : CatalanCore.Linalg.pivotRows (rowsCast p rows)=none := by simpa only [hp,Option.map_none] using ih.symm
        simp only [rowsCast] at hc
        simp only [hp,hc,Option.map_none]
      | some t =>
        rcases t with ⟨a,rs,neg⟩
        have hc : CatalanCore.Linalg.pivotRows (rowsCast p rows)=some (rowCast p a,rowsCast p rs,neg) := by
          simpa only [hp,Option.map_some,pivotCast] using ih.symm
        simp only [rowsCast] at hc
        simp only [hp,hc,Option.map_some,pivotCast]
        rfl

theorem rowCast_zipWith (p : ℕ) (f : ℕ→ℕ→ℕ) (g : ZMod p→ZMod p→ZMod p)
    (hf : ∀ a b,(f a b:ZMod p)=g (a:ZMod p) (b:ZMod p)) (xs ys : List ℕ) :
    rowCast p (List.zipWith f xs ys)=List.zipWith g (rowCast p xs) (rowCast p ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      change (f x y:ZMod p)::rowCast p (List.zipWith f xs ys)=
        g (x:ZMod p) (y:ZMod p)::List.zipWith g (rowCast p xs) (rowCast p ys)
      rw [hf,ih]

theorem nextRowsNat_cast (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (prev : ℕ) (row : List ℕ) (rest : List (List ℕ)) :
    rowsCast p (rest.map (fun rr=>List.zipWith (fun a b=>
      (subNat p (row.getD 0 0*a) (rr.getD 0 0*b)*inverseNat p C prev)%p) rr.tail row.tail))=
    (rowsCast p rest).map (fun rr=>List.zipWith (fun a b=>
      ((rowCast p row).getD 0 0*a-rr.getD 0 0*b)/(prev:ZMod p)) rr.tail (rowCast p row).tail) := by
  simp only [rowsCast,List.map_map]
  apply congrArg (fun f : List ℕ→List (ZMod p)=>rest.map f)
  funext rr
  have ht (xs : List ℕ) : (rowCast p xs).tail=rowCast p xs.tail := by simp [rowCast]
  dsimp only [Function.comp_apply]
  rw [ht,ht]
  apply rowCast_zipWith
  intro a b
  simp only [ZMod.natCast_mod,Nat.cast_mul,subNat_cast,(inverseNat_sound p C hC _).2,
    rowCast,cast_getD,div_eq_mul_inv]

theorem bareissLoopNat_cast (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n prev : ℕ) (neg : Bool) (rows : List (List ℕ)) :
    (bareissLoopNat p C n prev neg rows).map (fun x : ℕ=>(x:ZMod p))=
      CatalanCore.Linalg.bareissLoop n (prev:ZMod p) neg (rowsCast p rows) := by
  induction n using Nat.twoStepInduction generalizing prev neg rows with
  | zero => cases rows <;> simp [bareissLoopNat,CatalanCore.Linalg.bareissLoop,rowsCast]
  | one =>
    cases rows with
    | nil => rfl
    | cons row rows =>
      cases rows with
      | cons row2 rows2 =>
        cases row with
        | nil => rfl
        | cons x xs => cases xs <;> rfl
      | nil =>
        cases row with
        | nil => rfl
        | cons x xs =>
          cases xs with
          | cons y ys => rfl
          | nil => cases neg <;> simp [bareissLoopNat,CatalanCore.Linalg.bareissLoop,rowsCast,rowCast,subNat_cast]
  | more n ih0 ih1 =>
    have hguard :
        (rows.length=n+2 ∧ rows.all (fun row=>row.length==n+2) ∧ prev%p≠0) ↔
        ((rowsCast p rows).length=n+2 ∧ (rowsCast p rows).all (fun row=>row.length==n+2) ∧
          (prev:ZMod p)≠0) := by
      simp [rowsCast,rowCast,List.all_map,nat_mod_ne_zero_iff,Function.comp_def]
    by_cases hg : rows.length=n+2 ∧ rows.all (fun row=>row.length==n+2) ∧ prev%p≠0
    · rw [bareissLoopNat,if_pos hg,CatalanCore.Linalg.bareissLoop,if_pos (hguard.mp hg)]
      have hpfield := pivotRowsNat_cast p rows
      cases hp : pivotRowsNat p rows with
      | none =>
        rw [hp,Option.map_none] at hpfield
        rw [←hpfield]
        rfl
      | some t =>
        rcases t with ⟨row,rest,flip⟩
        rw [hp,Option.map_some] at hpfield
        rw [←hpfield]
        dsimp only [pivotCast]
        rw [ih1,nextRowsNat_cast p C hC]
        simp only [rowCast,cast_getD]
    · rw [bareissLoopNat,if_neg hg,CatalanCore.Linalg.bareissLoop,if_neg (fun h=>hg (hguard.mpr h))]
      rfl

theorem rowsCast_hankel (p n : ℕ) (m : List ℕ) :
    rowsCast p ((List.range n).map (fun i=>(List.range n).map (fun j=>m.getD (i+j) 0)))=
      (List.range n).map (fun i=>(List.range n).map (fun j=>(rowCast p m).getD (i+j) 0)) := by
  simp only [rowsCast,rowCast,List.map_map,Function.comp_def,cast_getD]

theorem bareissEvalNat_cast (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) :
    (bareissEvalNat p C n m).map (fun x : ℕ=>(x:ZMod p))=
      CatalanCore.Linalg.bareissEval n (rowCast p m) := by
  unfold bareissEvalNat CatalanCore.Linalg.bareissEval
  rw [bareissLoopNat_cast p C hC,rowsCast_hankel,Nat.cast_one]

theorem bareissEvalNat_sound (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) (v : ℕ)
    (h : bareissEvalNat p C n m=some v) :
    (v:ZMod p)=(CatalanCore.Linalg.hankel (rowCast p m) n 0).det := by
  have hc := bareissEvalNat_cast p C hC n m
  rw [h,Option.map_some] at hc
  exact CatalanCore.Linalg.bareissEval_sound n _ _ hc.symm

def scalarEvalNat (p : ℕ) (C : PrimeInverseTable) (n : ℕ) (m : List ℕ) : Option ℕ :=
  match djEvalNat p C n m with
  | some v=>some v
  | none=>bareissEvalNat p C n m

theorem scalarEvalNat_cast (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) :
    (scalarEvalNat p C n m).map (fun x : ℕ=>(x:ZMod p))=
      CatalanCore.Linalg.scalarEval n (rowCast p m) := by
  have hd := djEvalNat_cast p C hC n m
  change (djEvalNat p C n m).map (fun x : ℕ=>(x:ZMod p))=CatalanCore.Linalg.djEval n (rowCast p m) at hd
  unfold scalarEvalNat CatalanCore.Linalg.scalarEval
  cases hh : djEvalNat p C n m with
  | none =>
    rw [hh,Option.map_none] at hd
    rw [←hd]
    exact bareissEvalNat_cast p C hC n m
  | some v =>
    rw [hh,Option.map_some] at hd
    rw [←hd]
    rfl

theorem scalarEvalNat_sound (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) (v : ℕ)
    (h : scalarEvalNat p C n m=some v) :
    (v:ZMod p)=(CatalanCore.Linalg.hankel (rowCast p m) n 0).det := by
  have hc := scalarEvalNat_cast p C hC n m
  rw [h,Option.map_some] at hc
  exact CatalanCore.Linalg.scalarEval_sound n _ _ hc.symm

theorem scalarEvalNat_scalar (p : ℕ) [Fact p.Prime] (C : PrimeInverseTable)
    (hC : inverseTableCheck p C=true) (n : ℕ) (m : List ℕ) (v : ℕ)
    (h : scalarEvalNat p C n m=some v) :
    CatalanCore.Linalg.scalarEval n (rowCast p m)=some (v:ZMod p) := by
  have hc := scalarEvalNat_cast p C hC n m
  rw [h,Option.map_some] at hc
  exact hc.symm

#print axioms pivotRowsNat_cast
#print axioms rowCast_zipWith
#print axioms nextRowsNat_cast
#print axioms bareissLoopNat_cast
#print axioms bareissEvalNat_sound
#print axioms scalarEvalNat_sound
#print axioms scalarEvalNat_scalar
end CatalanCore.Li2.NVMod
