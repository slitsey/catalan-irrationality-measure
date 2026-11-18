module
public import CatalanCore.Linalg.Bareiss
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Int.Units
@[expose] public section
set_option Elab.async false
open Matrix Polynomial
namespace CatalanCore.Linalg
/-- A one-row/one-column border selected from a two-row/two-column border. -/
def borderCell {K ι : Type*} (A : Matrix ι ι K) (B : Matrix ι (Fin 2) K)
    (C : Matrix (Fin 2) ι K) (D : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    Matrix (ι⊕Unit) (ι⊕Unit) K :=
  Matrix.fromBlocks A (fun a _=>B a j) (fun _ a=>C i a) (fun _ _=>D i j)
/-- Sylvester's two-border determinant identity, with invertible central block. -/
theorem det_two_border_of_unit {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (B : Matrix ι (Fin 2) K) (C : Matrix (Fin 2) ι K)
    (D : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).det*A.det=
      (borderCell A B C D 0 0).det*(borderCell A B C D 1 1).det-
        (borderCell A B C D 0 1).det*(borderCell A B C D 1 0).det := by
  classical
  letI : Invertible A:=Matrix.invertibleOfIsUnitDet A hA
  let S:=D-C*⅟A*B
  have he (i j : Fin 2) : (borderCell A B C D i j).det=A.det*S i j := by
    unfold borderCell
    rw [Matrix.det_fromBlocks₁₁ A (fun a (_ : Unit)=>B a j)
      (fun (_ : Unit) a=>C i a) (fun (_ : Unit) (_ : Unit)=>D i j)]
    congr 1
    rw [Matrix.det_unique]
    rfl
  rw [Matrix.det_fromBlocks₁₁,he 0 0,he 1 1,he 0 1,he 1 0]
  change A.det*S.det*A.det=A.det*S 0 0*(A.det*S 1 1)-A.det*S 0 1*(A.det*S 1 0)
  rw [Matrix.det_fin_two]
  ring
private theorem map_borderCell {R S ι : Type*} (f : R→S)
    (A : Matrix ι ι R) (B : Matrix ι (Fin 2) R) (C : Matrix (Fin 2) ι R)
    (D : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    (borderCell A B C D i j).map f=borderCell (A.map f) (B.map f) (C.map f) (D.map f) i j := by
  ext a b
  cases a <;> cases b <;> rfl
/-- Polynomial perturbation removes the invertibility condition, including finite fields. -/
theorem det_two_border {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (B : Matrix ι (Fin 2) K) (C : Matrix (Fin 2) ι K)
    (D : Matrix (Fin 2) (Fin 2) K) :
    (Matrix.fromBlocks A B C D).det*A.det=
      (borderCell A B C D 0 0).det*(borderCell A B C D 1 1).det-
        (borderCell A B C D 0 1).det*(borderCell A B C D 1 0).det := by
  classical
  let AP : Matrix ι ι K[X]:=(Polynomial.X : K[X]) • (1 : Matrix ι ι K[X])+A.map Polynomial.C
  let BP : Matrix ι (Fin 2) K[X]:=B.map Polynomial.C
  let CP : Matrix (Fin 2) ι K[X]:=C.map Polynomial.C
  let DP : Matrix (Fin 2) (Fin 2) K[X]:=D.map Polynomial.C
  let f : K[X]→+*RatFunc K:=algebraMap K[X] (RatFunc K)
  have hf : Function.Injective f:=IsFractionRing.injective K[X] (RatFunc K)
  have hAP : AP.det≠0 := by
    intro hz
    have hh:=Polynomial.leadingCoeff_det_X_one_add_C A
    change AP.det.leadingCoeff=1 at hh
    rw [hz,Polynomial.leadingCoeff_zero] at hh
    exact zero_ne_one hh
  have hAF : IsUnit (AP.map f).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [←show f AP.det=(AP.map f).det from f.map_det AP]
    exact fun hz=>hAP (hf (by simpa only [map_zero] using hz))
  have hF:=det_two_border_of_unit (AP.map f) (BP.map f) (CP.map f) (DP.map f) hAF
  have hP : (Matrix.fromBlocks AP BP CP DP).det*AP.det=
      (borderCell AP BP CP DP 0 0).det*(borderCell AP BP CP DP 1 1).det-
        (borderCell AP BP CP DP 0 1).det*(borderCell AP BP CP DP 1 0).det := by
    apply hf
    simpa only [map_mul,map_sub,RingHom.map_det,RingHom.mapMatrix_apply,Matrix.fromBlocks_map,map_borderCell] using hF
  let g : K[X]→+*K:=Polynomial.evalRingHom 0
  have hgA : AP.map g=A := by
    ext i j
    simp [AP,g,Matrix.smul_apply,Matrix.map_apply]
  have hgB : BP.map g=B := by ext i j;simp [BP,g]
  have hgC : CP.map g=C := by ext i j;simp [CP,g]
  have hgD : DP.map g=D := by ext i j;simp [DP,g]
  have hh:=congrArg g hP
  simpa only [map_mul,map_sub,RingHom.map_det,RingHom.mapMatrix_apply,Matrix.fromBlocks_map,map_borderCell,
    hgA,hgB,hgC,hgD] using hh

noncomputable def endEquiv (n : ℕ) : Fin n⊕Unit≃Fin (n+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
@[simp] theorem endEquiv_inl (n : ℕ) (i : Fin n) : (endEquiv n (Sum.inl i)).val=i.val := by
  simp [endEquiv]
@[simp] theorem endEquiv_inr (n : ℕ) (u : Unit) : (endEquiv n (Sum.inr u)).val=n := by
  simp [endEquiv]
def firstIndex (n : ℕ) : Fin n⊕Unit→Fin (n+1)
  | .inl i=>i.succ
  | .inr _=>0
theorem firstIndex_bijective (n : ℕ) : Function.Bijective (firstIndex n) := by
  constructor
  · intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => congr 1;exact Fin.succ_inj.mp h
      | inr u => have hh:=congrArg Fin.val h;simp [firstIndex] at hh
    | inr u =>
      cases j with
      | inl j => have hh:=congrArg Fin.val h;simp [firstIndex] at hh
      | inr v => rfl
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact ⟨Sum.inr (),rfl⟩
    · exact ⟨Sum.inl j,rfl⟩
noncomputable def firstEquiv (n : ℕ) : Fin n⊕Unit≃Fin (n+1) :=
  Equiv.ofBijective (firstIndex n) (firstIndex_bijective n)
@[simp] theorem firstEquiv_inl (n : ℕ) (i : Fin n) : (firstEquiv n (Sum.inl i)).val=i.val+1:=rfl
@[simp] theorem firstEquiv_inr (n : ℕ) (u : Unit) : (firstEquiv n (Sum.inr u)).val=0:=rfl
/-- Different row and column reindexings preserve the square of the determinant. -/
theorem det_submatrix_equiv_square {K ι κ : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ K) (e f : ι≃κ) : (M.submatrix e f).det^2=M.det^2 := by
  let σ:=e.trans f.symm
  have he : M.submatrix e f=(M.submatrix f f).submatrix σ id := by
    ext i j
    simp [σ]
  rw [he,Matrix.det_permute,Matrix.det_submatrix_equiv_self]
  have hs : (Equiv.Perm.sign σ:ℤ)=1 ∨ (Equiv.Perm.sign σ:ℤ)=-1:=
    Int.isUnit_eq_one_or (Units.isUnit _)
  rcases hs with h | h <;> simp [h]
def middleIndex (n : ℕ) : Fin n⊕Fin 2→Fin (n+2)
  | .inl i=>i.succ.castSucc
  | .inr j=>if j=0 then 0 else Fin.last (n+1)
theorem middleIndex_bijective (n : ℕ) : Function.Bijective (middleIndex n) := by
  constructor
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        have hh:=congrArg Fin.val h
        have hij : i.val=j.val:=by simpa [middleIndex] using hh
        exact congrArg Sum.inl (Fin.ext hij)
      | inr j =>
        have hh:=congrArg Fin.val h
        fin_cases j <;> simp [middleIndex] at hh <;> omega
    | inr i =>
      cases y with
      | inl j =>
        have hh:=congrArg Fin.val h
        fin_cases i <;> simp [middleIndex] at hh <;> omega
      | inr j =>
        fin_cases i <;> fin_cases j <;> simp_all [middleIndex]
  · intro i
    by_cases h0 : i.val=0
    · refine ⟨Sum.inr 0,?_⟩
      apply Fin.ext
      simpa [middleIndex] using h0.symm
    · by_cases h1 : i.val=n+1
      · refine ⟨Sum.inr 1,?_⟩
        apply Fin.ext
        simpa [middleIndex] using h1.symm
      · refine ⟨Sum.inl ⟨i.val-1,by omega⟩,?_⟩
        apply Fin.ext
        dsimp [middleIndex]
        omega
noncomputable def middleEquiv (n : ℕ) : Fin n⊕Fin 2≃Fin (n+2) :=
  Equiv.ofBijective (middleIndex n) (middleIndex_bijective n)
@[simp] theorem middleEquiv_inl (n : ℕ) (i : Fin n) : (middleEquiv n (Sum.inl i)).val=i.val+1:=rfl
@[simp] theorem middleEquiv_zero (n : ℕ) : (middleEquiv n (Sum.inr 0)).val=0:=rfl
@[simp] theorem middleEquiv_one (n : ℕ) : (middleEquiv n (Sum.inr 1)).val=n+1:=rfl
def hankel {K : Type*} [Field K] (m : List K) (n j : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun a b=>m.getD (j+a.val+b.val) 0
/-- The Hankel Desnanot–Jacobi identity, including singular intermediate minors. -/
theorem hankel_dj_identity {K : Type*} [Field K] (m : List K) (k j : ℕ) :
    (hankel m (k+2) j).det*(hankel m k (j+2)).det=
      (hankel m (k+1) j).det*(hankel m (k+1) (j+2)).det-
        (hankel m (k+1) (j+1)).det^2 := by
  classical
  let edge (i : Fin 2) : ℕ:=if i=0 then 0 else k+1
  let A:=hankel m k (j+2)
  let B : Matrix (Fin k) (Fin 2) K:=fun i e=>m.getD (j+i.val+1+edge e) 0
  let C : Matrix (Fin 2) (Fin k) K:=fun e i=>B i e
  let D : Matrix (Fin 2) (Fin 2) K:=fun e f=>m.getD (j+edge e+edge f) 0
  have hbig : Matrix.fromBlocks A B C D=
      (hankel m (k+2) j).submatrix (middleEquiv k) (middleEquiv k) := by
    ext a b
    cases a with
    | inl a =>
      cases b with
      | inl b => simp [A,B,C,D,hankel,Matrix.fromBlocks,Matrix.transpose_apply];congr 2;omega
      | inr b => fin_cases b <;> simp [A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
    | inr a =>
      cases b with
      | inl b => fin_cases a <;> simp [A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
      | inr b => fin_cases a <;> fin_cases b <;> simp [A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
  have h00 : borderCell A B C D 0 0=
      (hankel m (k+1) j).submatrix (firstEquiv k) (firstEquiv k) := by
    ext a b
    cases a <;> cases b <;> simp [borderCell,A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
  have h11 : borderCell A B C D 1 1=
      (hankel m (k+1) (j+2)).submatrix (endEquiv k) (endEquiv k) := by
    ext a b
    cases a <;> cases b <;> simp [borderCell,A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
  have h01 : borderCell A B C D 0 1=
      (hankel m (k+1) (j+1)).submatrix (firstEquiv k) (endEquiv k) := by
    ext a b
    cases a <;> cases b <;> simp [borderCell,A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
  have h10 : borderCell A B C D 1 0=(borderCell A B C D 0 1).transpose := by
    ext a b
    cases a <;> cases b <;> simp [borderCell,A,B,C,D,edge,hankel,Matrix.fromBlocks,Matrix.transpose_apply] <;> congr 2 <;> omega
  have hh:=det_two_border A B C D
  rw [hbig,Matrix.det_submatrix_equiv_self,h00,Matrix.det_submatrix_equiv_self,
    h11,Matrix.det_submatrix_equiv_self,h10,Matrix.det_transpose,←sq,h01,
    det_submatrix_equiv_square] at hh
  exact hh

def djLoop {K : Type*} [Field K] [DecidableEq K] :
    ℕ→List K→List K→Option K
  | 0,_,cur=>cur.head?
  | fuel+1,prev,cur=>
    if prev.length=cur.length+2 ∧ 3≤cur.length ∧
        (List.range (cur.length-2)).all (fun j=>decide (prev.getD (j+2) 0≠0)) then
      let next:=(List.range (cur.length-2)).map (fun j=>
        (cur.getD j 0*cur.getD (j+2) 0-cur.getD (j+1) 0^2)/prev.getD (j+2) 0)
      djLoop fuel cur next
    else none
def djEval {K : Type*} [Field K] [DecidableEq K] (n : ℕ) (m : List K) : Option K :=
  if n=0 then some 1 else
    if m.length=2*n-1 then djLoop (n-1) (List.replicate (2*n+1) 1) m else none
def DJDivisorsNonzero {K : Type*} [Field K] (n : ℕ) (m : List K) : Prop :=
  ∀ k j : ℕ,k+2≤n→j+2*k≤2*n-2→(hankel m k j).det≠0
private theorem getD_map_range {K : Type*} (f : ℕ→K) (n j : ℕ) (d : K) (hj : j<n) :
    ((List.range n).map f).getD j d=f j := by
  rw [List.getD_eq_getElem _ d (by simpa using hj)]
  simp only [List.getElem_map,List.getElem_range]
private theorem djNext_spec {K : Type*} [Field K] (m : List K) (k : ℕ)
    (prev cur : List K)
    (hp : prev.length=cur.length+2)
    (hprev : ∀ j<prev.length,prev.getD j 0=(hankel m k j).det)
    (hcur : ∀ j<cur.length,cur.getD j 0=(hankel m (k+1) j).det)
    (hdiv : ∀ j<cur.length-2,prev.getD (j+2) 0≠0) :
    ∀ j<cur.length-2,
      ((List.range (cur.length-2)).map (fun j=>
        (cur.getD j 0*cur.getD (j+2) 0-cur.getD (j+1) 0^2)/prev.getD (j+2) 0)).getD j 0=
          (hankel m (k+2) j).det := by
  intro j hj
  rw [getD_map_range _ _ _ _ hj,hcur j (by omega),hcur (j+1) (by omega),
    hcur (j+2) (by omega),hprev (j+2) (by omega)]
  have hd : (hankel m k (j+2)).det≠0:=by rw [←hprev (j+2) (by omega)];exact hdiv j hj
  apply (div_eq_iff hd).mpr
  exact (hankel_dj_identity m k j).symm
private theorem djLoop_sound {K : Type*} [Field K] [DecidableEq K] (m : List K) :
    ∀ (fuel k : ℕ) (prev cur : List K) (v : K),
      prev.length=2*fuel+3→cur.length=2*fuel+1→
      (∀ j<prev.length,prev.getD j 0=(hankel m k j).det)→
      (∀ j<cur.length,cur.getD j 0=(hankel m (k+1) j).det)→
      djLoop fuel prev cur=some v→v=(hankel m (k+fuel+1) 0).det := by
  intro fuel
  induction fuel with
  | zero =>
    intro k prev cur v hp hc hprev hcur h
    cases cur with
    | nil => simp at hc
    | cons x xs =>
      have hv : x=v:=by simpa [djLoop] using h
      have hh:=hcur 0 (by simp)
      simpa [←hv] using hh
  | succ fuel ih =>
    intro k prev cur v hp hc hprev hcur h
    simp only [djLoop] at h
    split at h
    · rename_i hg
      let next:=(List.range (cur.length-2)).map (fun j=>
        (cur.getD j 0*cur.getD (j+2) 0-cur.getD (j+1) 0^2)/prev.getD (j+2) 0)
      have hd : ∀ j<cur.length-2,prev.getD (j+2) 0≠0:=by
        intro j hj
        exact of_decide_eq_true ((List.all_eq_true.mp hg.2.2) j (List.mem_range.mpr hj))
      have hn : next.length=2*fuel+1:=by simp only [next,List.length_map,List.length_range];omega
      have hnp:=djNext_spec m k prev cur hg.1 hprev hcur hd
      have hi:=ih (k+1) cur next v (by omega) hn hcur (by simpa [next] using hnp) h
      rw [show k+1+fuel+1=k+(fuel+1)+1 by omega] at hi
      exact hi
    · contradiction
theorem djEval_sound {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) (m : List K) (v : K) (h : djEval n m=some v) : v=(hankel m n 0).det := by
  cases n with
  | zero => simpa [djEval] using h.symm
  | succ n =>
    have hn : n+1≠0:=by omega
    have hlen : m.length=2*(n+1)-1:=by
      by_contra hno
      simp [djEval,hn,hno] at h
    have hr : djLoop n (List.replicate (2*(n+1)+1) 1) m=some v:=by
      simpa [djEval,hn,hlen] using h
    have hprev : ∀ j<(List.replicate (2*(n+1)+1) (1:K)).length,
        (List.replicate (2*(n+1)+1) (1:K)).getD j 0=(hankel m 0 j).det := by
      intro j hj
      rw [List.getD_eq_getElem _ 0 hj,Matrix.det_fin_zero]
      simp
    have hcur : ∀ j<m.length,m.getD j 0=(hankel m (0+1) j).det := by
      intro j hj
      rw [Matrix.det_fin_one]
      simp [hankel]
    have hi:=djLoop_sound m n 0 (List.replicate (2*(n+1)+1) 1) m v
      (by simp only [List.length_replicate];omega) (by omega) hprev hcur hr
    rw [show 0+n+1=n+1 by omega] at hi
    exact hi
private theorem djLoop_complete {K : Type*} [Field K] [DecidableEq K]
    (m : List K) (n : ℕ) (hdiv : DJDivisorsNonzero n m) :
    ∀ (fuel k : ℕ) (prev cur : List K),k+fuel+1=n→
      prev.length=2*fuel+3→cur.length=2*fuel+1→
      (∀ j<prev.length,prev.getD j 0=(hankel m k j).det)→
      (∀ j<cur.length,cur.getD j 0=(hankel m (k+1) j).det)→
      djLoop fuel prev cur=some ((hankel m (k+fuel+1) 0).det) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k prev cur hn hp hc hprev hcur
    cases cur with
    | nil => simp at hc
    | cons x xs =>
      have hh:=hcur 0 (by simp)
      simpa [djLoop] using congrArg some hh
  | succ fuel ih =>
    intro k prev cur hn hp hc hprev hcur
    have hd : ∀ j<cur.length-2,prev.getD (j+2) 0≠0:=by
      intro j hj
      rw [hprev (j+2) (by omega)]
      exact hdiv k (j+2) (by omega) (by omega)
    have hg : prev.length=cur.length+2 ∧ 3≤cur.length ∧
        (List.range (cur.length-2)).all (fun j=>decide (prev.getD (j+2) 0≠0)) := by
      refine ⟨by omega,by omega,?_⟩
      apply List.all_eq_true.mpr
      intro j hj
      exact decide_eq_true (hd j (List.mem_range.mp hj))
    let next:=(List.range (cur.length-2)).map (fun j=>
      (cur.getD j 0*cur.getD (j+2) 0-cur.getD (j+1) 0^2)/prev.getD (j+2) 0)
    have hnext : next.length=2*fuel+1:=by simp only [next,List.length_map,List.length_range];omega
    have hnp:=djNext_spec m k prev cur hg.1 hprev hcur hd
    have hi:=ih (k+1) cur next (by omega) (by omega) hnext hcur (by simpa [next] using hnp)
    rw [djLoop,if_pos hg]
    rw [show k+1+fuel+1=k+(fuel+1)+1 by omega] at hi
    exact hi
theorem djEval_of_nonzero_divisors {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) (m : List K) (hlen : m.length=2*n-1)
    (hdiv : DJDivisorsNonzero n m) : djEval n m=some ((hankel m n 0).det) := by
  cases n with
  | zero => simp [djEval]
  | succ n =>
    have hn : n+1≠0:=by omega
    rw [djEval,if_neg hn,if_pos hlen]
    have hprev : ∀ j<(List.replicate (2*(n+1)+1) (1:K)).length,
        (List.replicate (2*(n+1)+1) (1:K)).getD j 0=(hankel m 0 j).det := by
      intro j hj
      rw [List.getD_eq_getElem _ 0 hj,Matrix.det_fin_zero]
      simp
    have hcur : ∀ j<m.length,m.getD j 0=(hankel m (0+1) j).det := by
      intro j hj
      rw [Matrix.det_fin_one]
      simp [hankel]
    have hi:=djLoop_complete m (n+1) hdiv n 0 (List.replicate (2*(n+1)+1) 1) m
      (by omega) (by simp only [List.length_replicate];omega) (by omega) hprev hcur
    rw [show 0+n+1=n+1 by omega] at hi
    rw [show n+1-1=n by omega]
    exact hi
def pivotRows {K : Type*} [Field K] [DecidableEq K] :
    List (List K)→Option (List K×List (List K)×Bool)
  | []=>none
  | row::rows=>if row.getD 0 0≠0 then some (row,rows,false) else
      match pivotRows rows with
      | none=>none
      | some (a,rs,neg)=>some (a,row::rs,!neg)
theorem pivotRows_search {K : Type*} [Field K] [DecidableEq K] :
    ∀ (rows : List (List K)) (row : List K) (rest : List (List K)) (neg : Bool),
      pivotRows rows=some (row,rest,neg)→
      ∃ k : ℕ,k<rows.length ∧ row=rows.getD k [] ∧
        rest=rows.take k++rows.drop (k+1) ∧ row.getD 0 0≠0 ∧
        (if neg then (-1:ℤ) else 1)=(-1:ℤ)^k := by
  intro rows
  induction rows with
  | nil => intro row rest neg h;simp [pivotRows] at h
  | cons x xs ih =>
    intro row rest neg h
    by_cases hx : x.getD 0 0≠0
    · simp only [pivotRows,if_pos hx,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩:=h
      exact ⟨0,by simp,by simp,by simp,hx,by simp⟩
    · rw [pivotRows,if_neg hx] at h
      cases hr : pivotRows xs with
      | none => simp only [hr,reduceCtorEq] at h
      | some v =>
        obtain ⟨a,rs,b⟩:=v
        simp only [hr,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩:=h
        obtain ⟨k,hk,ha,hrs,hp,hs⟩:=ih a rs b hr
        refine ⟨k+1,by simpa using Nat.succ_lt_succ hk,by simpa using ha,?_,hp,?_⟩
        · simp [hrs]
        · rw [pow_succ]
          cases b <;>
            simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at hs ⊢ <;>
            rw [←hs] <;> ring
private theorem ofFn_removeNth {α : Type*} {n : ℕ} (f : Fin (n+1)→α) (p : Fin (n+1)) :
    List.ofFn (p.removeNth f)=(List.ofFn f).eraseIdx p := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx,p.isLt]
  · intro i hi hj
    rw [List.getElem_ofFn,List.getElem_eraseIdx]
    split_ifs with h
    · rw [Fin.removeNth_apply,Fin.succAbove_of_castSucc_lt _ _ (by exact h)]
      rw [List.getElem_ofFn]
      rfl
    · rw [Fin.removeNth_apply,Fin.succAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt h)]
      rw [List.getElem_ofFn]
      rfl
private theorem getD_ofFn_fin {R : Type*} {n : ℕ} (f : Fin n→R) (i : Fin n) (d : R) :
    (List.ofFn f).getD i d=f i := by
  rw [List.getD_eq_getElem _ d (by simpa using i.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]
/-- The executable pivot search supplies its own row permutation and its sign. -/
theorem pivotRows_matrix {K : Type*} [Field K] [DecidableEq K] (n : ℕ)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (row : List K) (rest : List (List K)) (neg : Bool)
    (h : pivotRows (matrixList M)=some (row,rest,neg)) :
    ∃ σ : Equiv.Perm (Fin (n+1)),matrixList (M.submatrix σ id)=row::rest ∧
      ((Equiv.Perm.sign σ:ℤ):K)=(if neg then -1 else 1) ∧ (M.submatrix σ id) 0 0≠0 := by
  classical
  obtain ⟨k,hk,ha,hrs,hp,hs⟩:=pivotRows_search _ _ _ _ h
  have hkN : k<n+1:=by simpa [matrixList] using hk
  let p : Fin (n+1):=⟨k,hkN⟩
  let f : Fin (n+1)→List K:=fun i=>List.ofFn (fun j=>M i j)
  have ha' : row=f p := by
    change row=(List.ofFn f).getD (p:ℕ) [] at ha
    rw [getD_ofFn_fin] at ha
    exact ha
  have hrs' : rest=List.ofFn (p.removeNth f) := by
    rw [ofFn_removeNth,List.eraseIdx_eq_take_drop_succ]
    exact hrs
  let σ:=(Fin.cycleRange p).symm
  have hrepr : matrixList (M.submatrix σ id)=row::rest := by
    change List.ofFn (f ∘ σ)=row::rest
    rw [←Fin.cons_removeNth_eq_comp_cycleRange_symm]
    rw [List.ofFn_succ]
    simpa only [Fin.cons_zero,Fin.cons_succ,ha',hrs']
  refine ⟨σ,hrepr,?_,?_⟩
  · have hc : (-1:K)^k=(if neg then -1 else 1):=by
      simpa only [map_pow,map_neg,map_one,apply_ite] using congrArg (Int.castRingHom K) hs.symm
    simpa [σ,Equiv.Perm.sign_symm,Fin.sign_cycleRange,p] using hc
  · have hlead : row.getD 0 0=(M.submatrix σ id) 0 0 := by
      have he:=congrArg (fun rows : List (List K)=>(rows.getD 0 []).getD 0 0) hrepr
      simpa only [matrixList,List.ofFn_succ,List.getD_cons_zero] using he.symm
    rw [←hlead]
    exact hp
def bareissLoop {K : Type*} [Field K] [DecidableEq K] :
    ℕ→K→Bool→List (List K)→Option K
  | 0,_,_,rows=>if rows=[] then some 1 else none
  | 1,_,neg,rows=>match rows with
    | [[x]]=>some (if neg then -x else x)
    | _=>none
  | n+2,prev,neg,rows=>
    if rows.length=n+2 ∧ rows.all (fun row=>row.length==n+2) ∧ prev≠0 then
      match pivotRows rows with
      | none=>none
      | some (row,rest,flip)=>
        let pv:=row.getD 0 0
        let next:=rest.map (fun rr=>List.zipWith (fun a b=>(pv*a-rr.getD 0 0*b)/prev) rr.tail row.tail)
        bareissLoop (n+1) pv (Bool.xor neg flip) next
    else none
private theorem zipWith_ofFn {α β γ : Type*} (f : α→β→γ) (n : ℕ)
    (xs : Fin n→α) (ys : Fin n→β) :
    List.zipWith f (List.ofFn xs) (List.ofFn ys)=List.ofFn (fun i=>f (xs i) (ys i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.zipWith_cons_cons,ih]
private theorem bareissNext_matrix {K : Type*} [Field K] (n : ℕ) (prev : K)
    (N : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    (List.ofFn (fun i : Fin n=>List.ofFn (fun j : Fin (n+1)=>N i.succ j))).map
      (fun rr=>List.zipWith (fun a b=>(N 0 0*a-rr.getD 0 0*b)/prev) rr.tail
        (List.ofFn (fun j : Fin (n+1)=>N 0 j)).tail)=matrixList (bareissStep prev N) := by
  unfold matrixList
  rw [List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,List.ofFn_succ,List.tail_cons,List.getD_cons_zero,zipWith_ofFn,bareissStep]
private theorem bareissStep_det {K : Type*} [Field K] (n : ℕ) (prev : K)
    (N : Matrix (Fin (n+2)) (Fin (n+2)) K) (hp : prev≠0) (hv : N 0 0≠0) :
    (N 0 0)^n*N.det=prev^(n+1)*(bareissStep prev N).det := by
  have he : prev • bareissStep prev N=pivotComp N := by
    ext i j
    simp only [bareissStep,pivotComp,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp
  have hd:=congrArg Matrix.det he
  rw [Matrix.det_smul,Fintype.card_fin] at hd
  have hh:=pivot_det N
  apply mul_left_cancel₀ hv
  calc
    N 0 0*((N 0 0)^n*N.det)=(N 0 0)^(n+1)*N.det:=by ring
    _=N 0 0*(pivotComp N).det:=hh
    _=N 0 0*(prev^(n+1)*(bareissStep prev N).det):=by rw [hd]

private def pivotSign {K : Type*} [Ring K] (b : Bool) : K:=if b then -1 else 1
private theorem bareissLoop_invariant {K : Type*} [Field K] [DecidableEq K] :
    ∀ (n : ℕ) (prev : K) (neg : Bool) (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (d : K),
      prev≠0→bareissLoop (n+1) prev neg (matrixList M)=some d→
        d*prev^n=pivotSign neg*M.det := by
  intro n
  induction n with
  | zero =>
    intro prev neg M d hp h
    have hr : matrixList M=[[M 0 0]]:=by simp [matrixList,List.ofFn_succ]
    rw [hr] at h
    simp only [bareissLoop,Option.some.injEq] at h
    rw [←h]
    cases neg <;> simp [pivotSign,Matrix.det_fin_one]
  | succ n ih =>
    intro prev neg M d hp h
    have hg : (matrixList M).length=n+2 ∧
        (matrixList M).all (fun row=>row.length==n+2) ∧ prev≠0 := by
      refine ⟨by simp [matrixList],?_,hp⟩
      apply List.all_eq_true.mpr
      intro row hr
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr
      simp
    rw [bareissLoop,if_pos hg] at h
    cases hr : pivotRows (matrixList M) with
    | none => simp only [hr,reduceCtorEq] at h
    | some v =>
      obtain ⟨row,rest,flip⟩:=v
      simp only [hr] at h
      obtain ⟨σ,hrepr,hsign,hpv⟩:=pivotRows_matrix (n+1) M row rest flip hr
      let N:=M.submatrix σ id
      have hout : matrixList N=(List.ofFn (fun j=>N 0 j))::
          List.ofFn (fun i : Fin (n+1)=>List.ofFn (fun j=>N i.succ j)) := by
        unfold matrixList
        rw [List.ofFn_succ]
      have hparts : row=List.ofFn (fun j=>N 0 j) ∧
          rest=List.ofFn (fun i : Fin (n+1)=>List.ofFn (fun j=>N i.succ j)) := by
        change matrixList N=row::rest at hrepr
        rw [hout] at hrepr
        exact ⟨(List.cons.inj hrepr).1.symm,(List.cons.inj hrepr).2.symm⟩
      have hlead : row.getD 0 0=N 0 0 := by
        rw [hparts.1]
        exact getD_ofFn_fin _ (0:Fin (n+2)) _
      have hnext : rest.map (fun rr=>List.zipWith
          (fun a b=>(row.getD 0 0*a-rr.getD 0 0*b)/prev) rr.tail row.tail)=
          matrixList (bareissStep prev N) := by
        rw [hlead,hparts.1,hparts.2]
        exact bareissNext_matrix (n+1) prev N
      rw [hnext,hlead] at h
      have hi:=ih (N 0 0) (Bool.xor neg flip) (bareissStep prev N) d hpv h
      have hd : N.det=pivotSign flip*M.det := by
        have hh : N.det=((Equiv.Perm.sign σ:ℤ):K)*M.det:=Matrix.det_permute σ M
        rw [hsign] at hh
        exact hh
      have hs : (pivotSign (Bool.xor neg flip):K)*pivotSign flip=pivotSign neg := by
        cases neg <;> cases flip <;> simp [pivotSign]
      have hstep:=bareissStep_det n prev N hp hpv
      apply mul_left_cancel₀ (pow_ne_zero n hpv)
      calc
        (N 0 0)^n*(d*prev^(n+1))=prev^(n+1)*(d*(N 0 0)^n):=by ring
        _=prev^(n+1)*(pivotSign (Bool.xor neg flip)*(bareissStep prev N).det):=by rw [hi]
        _=pivotSign (Bool.xor neg flip)*((N 0 0)^n*N.det):=by rw [hstep];ring
        _=(N 0 0)^n*(pivotSign (Bool.xor neg flip)*pivotSign flip*M.det):=by rw [hd];ring
        _=(N 0 0)^n*(pivotSign neg*M.det):=by rw [hs]
def bareissEval {K : Type*} [Field K] [DecidableEq K] (n : ℕ) (m : List K) : Option K :=
  bareissLoop n 1 false ((List.range n).map (fun i=>(List.range n).map (fun j=>m.getD (i+j) 0)))
private theorem matrixList_hankel {K : Type*} [Field K] (n : ℕ) (m : List K) :
    matrixList (hankel m n 0)=(List.range n).map (fun i=>(List.range n).map (fun j=>m.getD (i+j) 0)) := by
  unfold matrixList
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    apply List.ext_getElem
    · simp
    · intro j hji hjj
      simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range,hankel,Nat.zero_add]
theorem bareissEval_sound {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) (m : List K) (v : K) (h : bareissEval n m=some v) : v=(hankel m n 0).det := by
  cases n with
  | zero => simpa [bareissEval,bareissLoop] using h.symm
  | succ n =>
    have hr : bareissLoop (n+1) 1 false (matrixList (hankel m (n+1) 0))=some v := by
      rw [matrixList_hankel]
      exact h
    have hi:=bareissLoop_invariant n 1 false (hankel m (n+1) 0) v one_ne_zero hr
    simpa only [one_pow,mul_one,pivotSign,Bool.false_eq_true,ite_false,one_mul] using hi
def scalarEval {K : Type*} [Field K] [DecidableEq K] (n : ℕ) (m : List K) : Option K :=
  match djEval n m with
  | some v=>some v
  | none=>bareissEval n m
theorem scalarEval_sound {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) (m : List K) (v : K) (h : scalarEval n m=some v) : v=(hankel m n 0).det := by
  cases hd : djEval n m with
  | none =>
    have hh : bareissEval n m=some v:=by simpa only [scalarEval,hd] using h
    exact bareissEval_sound n m v hh
  | some d =>
    have hh : d=v:=by simpa only [scalarEval,hd,Option.some.injEq] using h
    rw [←hh]
    exact djEval_sound n m d hd

#print axioms det_two_border_of_unit
#print axioms det_two_border
#print axioms firstIndex_bijective
#print axioms det_submatrix_equiv_square
#print axioms middleIndex_bijective
#print axioms hankel_dj_identity
#print axioms djEval_sound
#print axioms djEval_of_nonzero_divisors
#print axioms pivotRows_search
#print axioms pivotRows_matrix
#print axioms bareissEval_sound
#print axioms scalarEval_sound
end CatalanCore.Linalg
