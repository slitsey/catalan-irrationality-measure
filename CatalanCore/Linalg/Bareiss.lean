module
public import CatalanCore.Linalg.RankDvd
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Linalg
open Matrix
/-- The exact matrix pivot step, shared by both structural list adapters. -/
def bareissStep {K : Type*} [Field K] {n : ℕ}
    (prev : K) (M : Matrix (Fin (n+1)) (Fin (n+1)) K) : Matrix (Fin n) (Fin n) K :=
  fun i j=>(M 0 0*M i.succ j.succ-M i.succ 0*M 0 j.succ)/prev
/-- Dimension recursion validates the previous and current pivot. -/
def bareissMatrix {K : Type*} [Field K] [DecidableEq K] :
    (n : ℕ)→K→Matrix (Fin n) (Fin n) K→Option K
  | 0,_,_=>some 1
  | 1,_,M=>some (M 0 0)
  | n+2,prev,M=>if M 0 0=0 ∨ prev=0 then none else
      bareissMatrix (n+1) (M 0 0) (bareissStep prev M)
/-- The Bareiss determinant invariant includes the previous-pivot factor. -/
theorem bareissMatrix_invariant {K : Type*} [Field K] [DecidableEq K] :
    ∀ (n : ℕ) (prev : K) (M : Matrix (Fin n) (Fin n) K) (d : K),
      prev≠0→bareissMatrix n prev M=some d→d*prev^(n-1)=M.det := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro prev M d hp h;simpa [bareissMatrix] using h.symm
  | one =>
    intro prev M d hp h
    simp only [bareissMatrix,Option.some.injEq] at h
    simp [←h,Matrix.det_fin_one]
  | more n ih0 ih1 =>
    intro prev M d hp h
    have hpv : M 0 0≠0 := by
      by_contra hz
      simp [bareissMatrix,hz] at h
    have hb : ¬(M 0 0=0 ∨ prev=0):=not_or.mpr ⟨hpv,hp⟩
    have hr : bareissMatrix (n+1) (M 0 0) (bareissStep prev M)=some d:=by
      simpa only [bareissMatrix,if_neg hb] using h
    have hi:=ih1 (M 0 0) (bareissStep prev M) d hpv hr
    have he : prev • bareissStep prev M=pivotComp M := by
      ext i j
      simp only [bareissStep,pivotComp,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
      field_simp
    have hd:=congrArg Matrix.det he
    rw [Matrix.det_smul,Fintype.card_fin] at hd
    have hv:=pivot_det M
    have hv' : (M 0 0)^n*M.det=(pivotComp M).det := by
      apply mul_left_cancel₀ hpv
      calc
        M 0 0*((M 0 0)^n*M.det)=(M 0 0)^(n+1)*M.det:=by ring
        _=M 0 0*(pivotComp M).det:=hv
    have hi' : d*(M 0 0)^n=(bareissStep prev M).det:=by simpa using hi
    apply mul_left_cancel₀ (pow_ne_zero n hpv)
    calc
      (M 0 0)^n*(d*prev^((n+2)-1))=prev^(n+1)*(d*(M 0 0)^n):=by rw [show n+2-1=n+1 by omega];ring
      _=prev^(n+1)*(bareissStep prev M).det:=by rw [hi']
      _=(pivotComp M).det:=hd
      _=(M 0 0)^n*M.det:=hv'.symm

def exactQuot (a b : ℤ) : Option ℤ :=
  if b≠0 ∧ a%b=0 then some (a/b) else none
def quotRow (prev piv lead : ℤ) : List ℤ→List ℤ→Option (List ℤ)
  | [],[]=>some []
  | x::xs,y::ys=>do
    let z←exactQuot (piv*x-lead*y) prev
    let zs←quotRow prev piv lead xs ys
    pure (z::zs)
  | _,_=>none
def quotRows (prev piv : ℤ) (prow : List ℤ) : List (List ℤ)→Option (List (List ℤ))
  | []=>some []
  | []::_=>none
  | (lead::row)::rows=>do
    let row'←quotRow prev piv lead row prow
    let rows'←quotRows prev piv prow rows
    pure (row'::rows')
def bareissAux : ℕ→ℤ→List (List ℤ)→Option ℤ
  | 0,_,[]=>some 1
  | 1,_,[[x]]=>some x
  | n+2,prev,(piv::prow)::rows=>
    if piv=0 ∨ prev=0 then none else do
      let next←quotRows prev piv prow rows
      bareissAux (n+1) piv next
  | _,_,_=>none
def bareissChecked (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) : Option ℤ :=
  bareissAux n 1 (List.ofFn (fun i=>List.ofFn (fun j=>M i j)))
private theorem exactQuot_spec (a b z : ℤ) (h : exactQuot a b=some z) :
    b≠0 ∧ b*z=a := by
  unfold exactQuot at h
  split at h
  · rename_i hp
    simp only [Option.some.injEq] at h
    refine ⟨hp.1,?_⟩
    rw [← h,mul_comm,Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hp.2)]
  · contradiction
private theorem quotRow_spec (prev piv lead : ℤ) :
    ∀ (xs ys zs : List ℤ),quotRow prev piv lead xs ys=some zs→
      xs.length=ys.length ∧ zs.length=xs.length ∧
        ∀ i : ℕ,i<xs.length→prev*zs.getD i 0=piv*xs.getD i 0-lead*ys.getD i 0 := by
  intro xs
  induction xs with
  | nil =>
    intro ys zs h
    cases ys with
    | nil => simp [quotRow] at h;subst zs;simp
    | cons y ys => simp [quotRow] at h
  | cons x xs ih =>
    intro ys zs h
    cases ys with
    | nil => simp [quotRow] at h
    | cons y ys =>
      cases hz : exactQuot (piv*x-lead*y) prev with
      | none => simp [quotRow,hz] at h
      | some z =>
        cases hrest : quotRow prev piv lead xs ys with
        | none => simp [quotRow,hz,hrest] at h
        | some zs' =>
          simp [quotRow,hz,hrest] at h
          subst zs
          obtain ⟨hlen,hzlen,he⟩:=ih ys zs' hrest
          refine ⟨by simp [hlen],by simp [hzlen],?_⟩
          intro i hi
          cases i with
          | zero => simpa using (exactQuot_spec _ _ _ hz).2
          | succ i =>
            have hi' : i<xs.length:=by simpa using hi
            simpa using he i hi'
private theorem list_eq_ofFn_getD {α : Type*} (xs : List α) (n : ℕ)
    (h : xs.length=n) (d : α) : xs=List.ofFn (fun i : Fin n=>xs.getD i d) := by
  apply List.ext_getElem
  · simpa using h
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact (List.getD_eq_getElem xs d hi).symm
private theorem quotRows_spec (prev piv : ℤ) (prow : List ℤ) (c : ℕ) (hprow : prow.length=c) :
    ∀ (rows next : List (List ℤ)),(∀ row∈rows,row.length=c+1)→
      quotRows prev piv prow rows=some next→
      next.length=rows.length ∧
      (∀ row∈next,row.length=c) ∧
      ∀ i : ℕ,i<rows.length→∀ j : ℕ,j<c→
        prev*(next.getD i []).getD j 0=
          piv*(rows.getD i []).getD (j+1) 0-
            (rows.getD i []).getD 0 0*prow.getD j 0 := by
  intro rows
  induction rows with
  | nil =>
    intro next hs h
    simp only [quotRows,Option.some.injEq] at h
    subst next;simp
  | cons row rows ih =>
    intro next hs h
    cases row with
    | nil => simp [quotRows] at h
    | cons lead xs =>
      have hxs : xs.length=c:=by simpa using hs (lead::xs) (by simp)
      have hrows : ∀ row∈rows,row.length=c+1:=fun row hr=>hs row (by simp [hr])
      cases hx : quotRow prev piv lead xs prow with
      | none => simp [quotRows,hx] at h
      | some zs =>
        cases hrest : quotRows prev piv prow rows with
        | none => simp [quotRows,hx,hrest] at h
        | some next' =>
          simp [quotRows,hx,hrest] at h
          subst next
          obtain ⟨hlen,hshape,he⟩:=ih next' hrows hrest
          obtain ⟨hxy,hzs,hz⟩:=quotRow_spec prev piv lead xs prow zs hx
          refine ⟨by simp [hlen],?_,?_⟩
          · intro row hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hzs.trans hxs
            · exact hshape row hr
          · intro i hi j hj
            cases i with
            | zero =>
              have hh:=hz j (by omega)
              simpa using hh
            | succ i =>
              have hh:=he i (by simpa using hi) j hj
              simpa using hh
private theorem getD_ofFn_fin {R : Type*} {n : ℕ} (f : Fin n→R) (i : Fin n) (d : R) :
    (List.ofFn f).getD i d=f i := by
  rw [List.getD_eq_getElem _ d (by simpa using i.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]
/-- Structural list encoding used by both exact determinant adapters. -/
def matrixList {R : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : List (List R) :=
  List.ofFn (fun i=>List.ofFn (fun j=>M i j))
def listMatrix {R : Type*} [Zero R] (n : ℕ) (rows : List (List R)) : Matrix (Fin n) (Fin n) R :=
  fun i j=>(rows.getD i []).getD j 0
private theorem matrixList_listMatrix {R : Type*} [Zero R] (n : ℕ) (rows : List (List R))
    (hlen : rows.length=n) (hs : ∀ row∈rows,row.length=n) :
    matrixList (listMatrix n rows)=rows := by
  calc
    matrixList (listMatrix n rows)=List.ofFn (fun i : Fin n=>rows.getD i []) := by
      unfold matrixList listMatrix
      congr 1
      funext i
      have hi : (i:ℕ)<rows.length:=by omega
      have hm : rows.getD i []∈rows:=by
        rw [List.getD_eq_getElem rows [] hi]
        exact List.getElem_mem hi
      exact (list_eq_ofFn_getD (rows.getD i []) n (hs _ hm) 0).symm
    _=rows:=(list_eq_ofFn_getD rows n hlen []).symm
private theorem bareissAux_cast :
    ∀ (n : ℕ) (prev : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (d : ℤ),
      prev≠0→bareissAux n prev (matrixList M)=some d→
        bareissMatrix n (prev:ℚ) (M.map (Int.castRingHom ℚ))=some (d:ℚ) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro prev M d hp h
    simp [bareissAux,matrixList] at h
    simp [bareissMatrix,←h]
  | one =>
    intro prev M d hp h
    simp [bareissAux,matrixList,List.ofFn_succ] at h
    simp [bareissMatrix,Matrix.map_apply,←h]
  | more n ih0 ih1 =>
    intro prev M d hp h
    let prow:=List.ofFn (fun j : Fin (n+1)=>M 0 j.succ)
    let rows:=List.ofFn (fun i : Fin (n+1)=>M i.succ 0::List.ofFn (fun j : Fin (n+1)=>M i.succ j.succ))
    have hrepr : matrixList M=(M 0 0::prow)::rows:=by
      simp only [matrixList,prow,rows,List.ofFn_succ]
    rw [hrepr] at h
    have hpv : M 0 0≠0:=by
      by_contra hz
      simp [bareissAux,hz] at h
    have hb : ¬(M 0 0=0 ∨ prev=0):=not_or.mpr ⟨hpv,hp⟩
    simp only [bareissAux,if_neg hb] at h
    cases hnext : quotRows prev (M 0 0) prow rows with
    | none => simp [hnext] at h
    | some next =>
      have hrec : bareissAux (n+1) (M 0 0) next=some d:=by simpa [hnext] using h
      have hprow : prow.length=n+1:=by simp [prow]
      have hshape : ∀ row∈rows,row.length=(n+1)+1 := by
        intro row hr
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr
        simp
      have hs:=quotRows_spec prev (M 0 0) prow (n+1) hprow rows next hshape hnext
      have hlen : next.length=n+1:=by simpa [rows] using hs.1
      let N:=listMatrix (n+1) next
      have hNrepr : matrixList N=next:=matrixList_listMatrix (n+1) next hlen hs.2.1
      have hpQ : (prev:ℚ)≠0:=by exact_mod_cast hp
      have hpvQ : ((M 0 0:ℤ):ℚ)≠0:=by exact_mod_cast hpv
      have hN : N.map (Int.castRingHom ℚ)=bareissStep (prev:ℚ) (M.map (Int.castRingHom ℚ)) := by
        ext i j
        have he:=hs.2.2 i (by simpa [rows] using i.isLt) j j.isLt
        have heZ : prev*N i j=M 0 0*M i.succ j.succ-M i.succ 0*M 0 j.succ := by
          simpa only [N,listMatrix,rows,prow,getD_ofFn_fin,List.getD_cons_zero,List.getD_cons_succ] using he
        have heQ : (prev:ℚ)*(N i j:ℚ)=
            (M 0 0:ℚ)*(M i.succ j.succ:ℚ)-(M i.succ 0:ℚ)*(M 0 j.succ:ℚ):=by exact_mod_cast heZ
        simp only [Matrix.map_apply,bareissStep,Int.coe_castRingHom]
        apply (eq_div_iff hpQ).mpr
        simpa only [mul_comm] using heQ
      have hi:=ih1 (M 0 0) N d hpv (by rw [hNrepr];exact hrec)
      rw [hN] at hi
      change (if ((M 0 0:ℤ):ℚ)=0 ∨ (prev:ℚ)=0 then none else
        bareissMatrix (n+1) ((M 0 0:ℤ):ℚ)
          (bareissStep (prev:ℚ) (M.map (Int.castRingHom ℚ))))=some (d:ℚ)
      rw [if_neg (not_or.mpr ⟨hpvQ,hpQ⟩)]
      exact hi
/-- Successful checked exact divisions return precisely the integer determinant. -/
theorem bareiss_sound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (h : bareissChecked n M=some d) : d=M.det := by
  have hc:=bareissAux_cast n 1 M d (by decide) h
  have hd:=bareissMatrix_invariant n (1:ℚ) (M.map (Int.castRingHom ℚ)) (d:ℚ) (by decide) hc
  simp only [one_pow,mul_one] at hd
  simp only [Int.coe_castRingHom] at hd
  rw [←Int.cast_det] at hd
  exact_mod_cast hd
#print axioms bareissMatrix_invariant
#print axioms exactQuot_spec
#print axioms quotRow_spec
#print axioms quotRows_spec
#print axioms bareissAux_cast
#print axioms bareiss_sound
#print axioms list_eq_ofFn_getD
end CatalanCore.Linalg
