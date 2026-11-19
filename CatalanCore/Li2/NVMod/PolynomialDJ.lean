module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialLists
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2.NVMod.PolynomialCert
open CatalanCore.Linalg
/-- Structural integer DJ; the exact division is part of the checked computation. -/
def djStepZ : List ℤ→List ℤ→Option (List ℤ)
  | c0::c1::c2::cs,p0::p1::p2::ps=>
      let num:=c0*c2-c1*c1
      if p2≠0 ∧ num%p2=0 then
        match djStepZ (c1::c2::cs) (p1::p2::ps) with
        | some r=>some (num/p2::r)
        | none=>none
      else none
  | _,_=>some []
def djLoopZ : ℕ→List ℤ→List ℤ→Option ℤ
  | 0,_,cur=>cur.head?
  | f+1,prev,cur=>match djStepZ cur prev with
    | some nxt=>djLoopZ f cur nxt
    | none=>none
def djEvalZ (n : ℕ) (m : List ℤ) : Option ℤ :=
  if n=0 then some 1 else
    if m.length=2*n-1 then djLoopZ (n-1) (List.replicate (2*n+1) 1) m else none

theorem stepZ_spec : ∀ (cur prev nxt : List ℤ),prev.length=cur.length+2→
    djStepZ cur prev=some nxt→
    nxt.length=cur.length-2 ∧ ∀ j<nxt.length,
      prev.getD (j+2) 0≠0 ∧
      (nxt.getD j 0:ℚ)=
        ((cur.getD j 0:ℚ)*(cur.getD (j+2) 0:ℚ)-(cur.getD (j+1) 0:ℚ)^2)/
          (prev.getD (j+2) 0:ℚ) := by
  intro cur
  induction cur with
  | nil=>
    intro prev nxt hp h
    simp only [djStepZ,Option.some.injEq] at h
    subst nxt
    simp
  | cons a tail ih=>
    intro prev nxt hp h
    cases tail with
    | nil=>simp only [djStepZ,Option.some.injEq] at h;subst nxt;simp
    | cons b tail=>
      cases tail with
      | nil=>simp only [djStepZ,Option.some.injEq] at h;subst nxt;simp
      | cons c cs=>
        cases prev with
        | nil=>simp at hp
        | cons p0 ps=>
          cases ps with
          | nil=>simp at hp
          | cons p1 ps=>
            cases ps with
            | nil=>simp at hp
            | cons p2 ps=>
              simp only [djStepZ] at h
              split at h
              · rename_i hg
                cases ht : djStepZ (b::c::cs) (p1::p2::ps) with
                | none=>simp [ht] at h
                | some ns=>
                  simp only [ht,Option.some.injEq] at h
                  subst nxt
                  have hi := ih (p1::p2::ps) ns (by simpa using hp) ht
                  refine ⟨by simp only [List.length_cons] at *;omega,?_⟩
                  intro j hj
                  cases j with
                  | zero=>
                    refine ⟨hg.1,?_⟩
                    simp only [List.getD_cons_zero,List.getD_cons_succ]
                    rw [Int.cast_div_charZero (Int.dvd_of_emod_eq_zero hg.2)]
                    push_cast
                    ring
                  | succ j=>
                    simpa only [List.getD_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc] using
                      hi.2 j (by simpa using hj)
              · simp at h

private theorem loopZ_sound (m : List ℤ) :
    ∀ (fuel k : ℕ) (prev cur : List ℤ) (v : ℤ),
      prev.length=2*fuel+3→cur.length=2*fuel+1→
      (∀ j<prev.length,(prev.getD j 0:ℚ)=(hankel (m.map (Int.castRingHom ℚ)) k j).det)→
      (∀ j<cur.length,(cur.getD j 0:ℚ)=(hankel (m.map (Int.castRingHom ℚ)) (k+1) j).det)→
      djLoopZ fuel prev cur=some v→
      (v:ℚ)=(hankel (m.map (Int.castRingHom ℚ)) (k+fuel+1) 0).det := by
  intro fuel
  induction fuel with
  | zero=>
    intro k prev cur v hp hc hprev hcur h
    cases cur with
    | nil=>simp at hc
    | cons x xs=>
      have hv : x=v:=by simpa [djLoopZ] using h
      simpa [←hv] using hcur 0 (by simp)
  | succ fuel ih=>
    intro k prev cur v hp hc hprev hcur h
    cases ht : djStepZ cur prev with
    | none=>simp [djLoopZ,ht] at h
    | some nxt=>
      have hs := stepZ_spec cur prev nxt (by omega) ht
      have hn : nxt.length=2*fuel+1:=by omega
      have hnext : ∀ j<nxt.length,(nxt.getD j 0:ℚ)=
          (hankel (m.map (Int.castRingHom ℚ)) (k+2) j).det := by
        intro j hj
        rw [(hs.2 j hj).2,hcur j (by omega),hcur (j+2) (by omega),
          hcur (j+1) (by omega),hprev (j+2) (by omega)]
        have hd : (hankel (m.map (Int.castRingHom ℚ)) k (j+2)).det≠0 := by
          rw [←hprev (j+2) (by omega)]
          exact_mod_cast (hs.2 j hj).1
        apply (div_eq_iff hd).mpr
        exact (hankel_dj_identity (m.map (Int.castRingHom ℚ)) k j).symm
      have hh : djLoopZ fuel cur nxt=some v:=by simpa [djLoopZ,ht] using h
      have hi := ih (k+1) cur nxt v (by omega) hn hcur
        (by simpa only [Nat.add_assoc] using hnext) hh
      rw [show k+1+fuel+1=k+(fuel+1)+1 by omega] at hi
      exact hi
/-- NZ1: checked integer divisions produce the actual rational Hankel determinant. -/
theorem djEvalZ_sound (n : ℕ) (m : List ℤ) (v : ℤ) (h : djEvalZ n m=some v) :
    (v:ℚ)=(hankel (m.map (Int.castRingHom ℚ)) n 0).det := by
  cases n with
  | zero=>simpa [djEvalZ] using congrArg (fun x : Option ℤ=>x.map (Int.castRingHom ℚ)) h.symm
  | succ n=>
    have hlen : m.length=2*(n+1)-1:=by
      by_contra hno
      simp [djEvalZ,hno] at h
    have hr : djLoopZ n (List.replicate (2*(n+1)+1) 1) m=some v:=by
      simpa [djEvalZ,hlen] using h
    suffices hh : (v:ℚ)=(hankel (m.map (Int.castRingHom ℚ)) (0+n+1) 0).det by
      rw [Nat.zero_add] at hh
      exact hh
    apply loopZ_sound m n 0 _ m v (by simp;omega) (by omega) ?_ ?_ hr
    · intro j hj
      rw [List.getD_eq_getElem _ 0 hj,Matrix.det_fin_zero]
      simp
    · intro j hj
      rw [Matrix.det_fin_one]
      simp only [hankel,Matrix.of_apply,Fin.val_zero,zero_add,add_zero]
      simpa only [map_zero,Int.coe_castRingHom] using (List.getD_map m 0 (n:=j) (Int.castRingHom ℚ)).symm
/-- The integer output is the actual integer determinant. -/
theorem djEvalZ_det (n : ℕ) (m : List ℤ) (v : ℤ) (h : djEvalZ n m=some v) :
    v=(Matrix.of fun i j : Fin n=>m.getD (i.val+j.val) 0).det := by
  apply Int.cast_injective (α:=ℚ)
  change (v:ℚ)=(Int.castRingHom ℚ) (Matrix.of fun i j : Fin n=>m.getD (i.val+j.val) 0).det
  rw [RingHom.map_det]
  have hm : (Int.castRingHom ℚ).mapMatrix (Matrix.of fun i j : Fin n=>m.getD (i.val+j.val) 0)=
      hankel (m.map (Int.castRingHom ℚ)) n 0 := by
    apply Matrix.ext
    intro i j
    change (m.getD (i.val+j.val) 0:ℚ)=(m.map (Int.castRingHom ℚ)).getD (0+i.val+j.val) 0
    simpa only [zero_add,map_zero,Int.coe_castRingHom] using
      (List.getD_map m 0 (n:=i.val+j.val) (Int.castRingHom ℚ)).symm
  rw [hm]
  exact djEvalZ_sound n m v h
#print axioms djEvalZ_sound
#print axioms djEvalZ_det
end CatalanCore.Li2.NVMod.PolynomialCert



