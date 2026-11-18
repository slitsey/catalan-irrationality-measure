module
public import CatalanCore.Li2.NV.ScaledGram
public import CatalanCore.Li2.NV.TieFree
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
private theorem det_corner_add {F : Type*} [CommRing F] (d : ℕ)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) F) (t : F) :
    (Matrix.of fun i j => A i j + if i=Fin.last d ∧ j=Fin.last d then t else 0).det =
      A.det+t*(A.submatrix Fin.castSucc Fin.castSucc).det := by
  classical
  let last := Fin.last d
  let v : Fin (d+1) → F := fun j => if j=last then t else 0
  have he : (Matrix.of fun i j => A i j + if i=last ∧ j=last then t else 0)=
      A.updateRow last (A last+v) := by
    ext i j
    by_cases hi : i=last <;> by_cases hj : j=last <;>
      simp [Matrix.updateRow,Function.update,hi,hj,v]
  rw [he,Matrix.det_updateRow_add,Matrix.updateRow_eq_self]
  congr 1
  rw [Matrix.det_succ_row _ last]
  rw [Finset.sum_eq_single last]
  · have hminor : (A.updateRow last v).submatrix last.succAbove last.succAbove =
        A.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [last,Matrix.submatrix,Matrix.updateRow,Fin.succAbove_last]
    rw [hminor]
    simp [v,last,pow_add,←mul_pow]
  · intro j hj hjl
    simp [Matrix.updateRow_self,v,hjl]
  · simp
private theorem det_schur_corner {F α : Type*} [Field F] [Fintype α] [DecidableEq α]
    (d : ℕ) (A : Matrix α α F) (B : Matrix α (Fin (d+1)) F)
    (C : Matrix (Fin (d+1)) α F) (D : Matrix (Fin (d+1)) (Fin (d+1)) F)
    (t u : F) (hA : A.det≠0)
    (hCB : C*A⁻¹*B = Matrix.of fun i j => if i=Fin.last d ∧ j=Fin.last d then u else 0) :
    (Matrix.fromBlocks A B C
      (Matrix.of fun i j => D i j + if i=Fin.last d ∧ j=Fin.last d then t else 0)).det =
      A.det*(D.det+(t-u)*(D.submatrix Fin.castSucc Fin.castSucc).det) := by
  classical
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  rw [Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv,hCB]
  have he : (Matrix.of fun i j => D i j + if i=Fin.last d ∧ j=Fin.last d then t else 0) -
      (Matrix.of fun i j => if i=Fin.last d ∧ j=Fin.last d then u else 0) =
      Matrix.of (fun i j => D i j + if i=Fin.last d ∧ j=Fin.last d then t-u else 0) := by
    ext i j
    by_cases h : i=Fin.last d ∧ j=Fin.last d <;> simp [h] <;> ring
  rw [he,det_corner_add]
private theorem hankel_schur_quotient {F : Type*} [Field F] (d : ℕ) (f : ℕ→F)
    (hH : (Matrix.of fun i j : Fin d => f (i.val+j.val)).det≠0) :
    (Matrix.of fun i j : Fin (d+1) => f (i.val+j.val)).det /
      (Matrix.of fun i j : Fin d => f (i.val+j.val)).det =
    f (2*d) - ∑ i : Fin d, ∑ j : Fin d,
      f (d+i.val)*(Matrix.of fun i j : Fin d => f (i.val+j.val))⁻¹ i j*f (j.val+d) := by
  classical
  let H : Matrix (Fin d) (Fin d) F := Matrix.of fun i j => f (i.val+j.val)
  let B : Matrix (Fin d) (Fin 1) F := fun i _ => f (i.val+d)
  let C : Matrix (Fin 1) (Fin d) F := fun _ j => f (d+j.val)
  let D : Matrix (Fin 1) (Fin 1) F := fun _ _ => f (2*d)
  let Hp : Matrix (Fin (d+1)) (Fin (d+1)) F := fun i j => f (i.val+j.val)
  have he : Matrix.fromBlocks H B C D = Hp.submatrix finSumFinEquiv finSumFinEquiv := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · rfl
    · have hi : j=0 := Subsingleton.elim _ _
      subst j
      simp [Hp,B]
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      simp [Hp,C]
    · have hi : i=0 := Subsingleton.elim _ _
      have hj : j=0 := Subsingleton.elim _ _
      subst i; subst j
      simp [Hp,D,two_mul]
  letI : Invertible H := Matrix.invertibleOfIsUnitDet H (isUnit_iff_ne_zero.mpr hH)
  have hd := Matrix.det_fromBlocks₁₁ H B C D
  rw [he,Matrix.det_submatrix_equiv_self,Matrix.invOf_eq_nonsing_inv,
    Matrix.det_eq_elem_of_subsingleton _ (0:Fin 1)] at hd
  have hq : (C*H⁻¹*B) 0 0 = ∑ i : Fin d, ∑ j : Fin d,
      f (d+i.val)*H⁻¹ i j*f (j.val+d) := by
    simp only [Matrix.mul_apply,C,B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  simp only [Matrix.sub_apply,D] at hd
  rw [hq] at hd
  change Hp.det/H.det=_
  rw [hd]
  exact mul_div_cancel_left₀ _ hH
private theorem scalar_block_inverse {F S : Type*} [Field F] [Fintype S] [DecidableEq S]
    (d : ℕ) (H : Matrix (Fin d) (Fin d) F) (u : S→F)
    (hH : H.det≠0) (hu : ∀ s,u s≠0) :
    (Matrix.blockDiagonal (fun s => u s • H))⁻¹ =
      Matrix.blockDiagonal (fun s => (u s)⁻¹ • H⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [←Matrix.blockDiagonal_mul]
  have he : (fun s => (u s • H)*((u s)⁻¹ • H⁻¹)) = fun _ : S => (1:Matrix (Fin d) (Fin d) F) := by
    funext s
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hH)]
    simp [hu s]
  rw [he]
  exact Matrix.blockDiagonal_one
private theorem scalar_block_det {F S : Type*} [Field F] [Fintype S] [DecidableEq S]
    (d : ℕ) (H : Matrix (Fin d) (Fin d) F) (u : S→F) :
    (Matrix.blockDiagonal (fun s => u s • H)).det = ∏ s,u s^d*H.det := by
  simp only [Matrix.det_blockDiagonal,Matrix.det_smul,Fintype.card_fin]
private theorem scalar_block_contraction {F S : Type*} [Field F] [Fintype S] [DecidableEq S]
    (d e : ℕ) (H : Matrix (Fin d) (Fin d) F) (u t : S→F) (v : Fin d→F)
    (last : Fin e) (hH : H.det≠0) (hu : ∀ s,u s≠0) :
    let A := Matrix.blockDiagonal (fun s => u s • H)
    let B : Matrix (Fin d × S) (Fin e) F := fun P j => if j=last then t P.2*v P.1 else 0
    B.transpose*A⁻¹*B = Matrix.of (fun i j => if i=last ∧ j=last then
      (∑ s,t s^2/u s)*(∑ a : Fin d, ∑ b : Fin d,v a*H⁻¹ a b*v b) else 0) := by
  classical
  dsimp only
  rw [scalar_block_inverse d H u hH hu]
  ext i j
  by_cases hi : i=last <;> by_cases hj : j=last
  · subst i; subst j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,ite_true,Matrix.of_apply,true_and,
      Finset.sum_mul,Fintype.sum_prod_type,Matrix.blockDiagonal_apply,Matrix.smul_apply,smul_eq_mul]
    simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro s hs
    ring
  · simp [Matrix.mul_apply,hj]
  · simp [Matrix.mul_apply,Matrix.transpose_apply,hi]
  · simp [Matrix.mul_apply,Matrix.transpose_apply,hi,hj]

private theorem hankel_arrow_det {F S : Type*} [Field F] [Fintype S] [DecidableEq S]
    (d e : ℕ) (f g : ℕ→F) (u t : S→F) (u0 : F)
    (hH : (Matrix.of fun i j : Fin d => f (i.val+j.val)).det≠0)
    (hu : ∀ s,u s≠0) :
    let H : Matrix (Fin d) (Fin d) F := Matrix.of fun i j => f (i.val+j.val)
    let A := Matrix.blockDiagonal (fun s => u s • H)
    let B : Matrix (Fin d × S) (Fin (e+1)) F :=
      fun P j => if j=Fin.last e then t P.2*f (P.1.val+d) else 0
    let S0 := ∑ s,t s^2/u s
    let D : Matrix (Fin (e+1)) (Fin (e+1)) F :=
      fun i j => u0*g (i.val+j.val) +
        if i=Fin.last e ∧ j=Fin.last e then S0*f (2*d) else 0
    (Matrix.fromBlocks A B B.transpose D).det =
      (∏ s,u s^d*H.det)*
      (u0^(e+1)*(Matrix.of fun i j : Fin (e+1) => g (i.val+j.val)).det +
        S0*((Matrix.of fun i j : Fin (d+1) => f (i.val+j.val)).det/H.det)*
          u0^e*(Matrix.of fun i j : Fin e => g (i.val+j.val)).det) := by
  classical
  dsimp only
  let H : Matrix (Fin d) (Fin d) F := Matrix.of fun i j => f (i.val+j.val)
  let Hu : Matrix (Fin (e+1)) (Fin (e+1)) F := Matrix.of fun i j => g (i.val+j.val)
  let A := Matrix.blockDiagonal (fun s => u s • H)
  let B : Matrix (Fin d × S) (Fin (e+1)) F :=
    fun P j => if j=Fin.last e then t P.2*f (P.1.val+d) else 0
  let S0 := ∑ s,t s^2/u s
  let q := ∑ a : Fin d, ∑ b : Fin d, f (a.val+d)*H⁻¹ a b*f (b.val+d)
  have hAdet : A.det≠0 := by
    rw [scalar_block_det d H u]
    exact Finset.prod_ne_zero_iff.mpr (fun s hs => mul_ne_zero (pow_ne_zero _ (hu s)) hH)
  have hc := scalar_block_contraction d (e+1) H u t (fun i => f (i.val+d)) (Fin.last e) hH hu
  have hd := det_schur_corner e A B B.transpose (u0 • Hu) (S0*f (2*d)) (S0*q) hAdet hc
  have hminor : (u0 • Hu).submatrix Fin.castSucc Fin.castSucc =
      u0 • (Matrix.of fun i j : Fin e => g (i.val+j.val)) := rfl
  rw [scalar_block_det d H u,Matrix.det_smul,hminor,Matrix.det_smul,Fintype.card_fin,Fintype.card_fin] at hd
  have hq := hankel_schur_quotient d f hH
  have hq' : (Matrix.of fun i j : Fin (d+1) => f (i.val+j.val)).det/H.det = f (2*d)-q := by
    simpa only [q,H,Nat.add_comm] using hq
  refine hd.trans ?_
  change (∏ s,u s^d*H.det)*
      (u0^(e+1)*Hu.det+(S0*f (2*d)-S0*q)*(u0^e*(Matrix.of fun i j : Fin e => g (i.val+j.val)).det)) =
    (∏ s,u s^d*H.det)*
      (u0^(e+1)*Hu.det+S0*((Matrix.of fun i j : Fin (d+1) => f (i.val+j.val)).det/H.det)*
        u0^e*(Matrix.of fun i j : Fin e => g (i.val+j.val)).det)
  rw [hq']
  ring
private theorem hankel_arrow_det_pos {F S : Type*} [Field F] [Fintype S] [DecidableEq S]
    (d e : ℕ) (he : 0<e) (f g : ℕ→F) (u t : S→F) (u0 : F)
    (hH : (Matrix.of fun i j : Fin d => f (i.val+j.val)).det≠0)
    (hu : ∀ s,u s≠0) :
    let H : Matrix (Fin d) (Fin d) F := Matrix.of fun i j => f (i.val+j.val)
    let A := Matrix.blockDiagonal (fun s => u s • H)
    let B : Matrix (Fin d × S) (Fin e) F :=
      fun P j => if j.val+1=e then t P.2*f (P.1.val+d) else 0
    let S0 := ∑ s,t s^2/u s
    let D : Matrix (Fin e) (Fin e) F :=
      fun i j => u0*g (i.val+j.val) +
        if i.val+1=e ∧ j.val+1=e then S0*f (2*d) else 0
    (Matrix.fromBlocks A B B.transpose D).det =
      (∏ s,u s^d*H.det)*
      (u0^e*(Matrix.of fun i j : Fin e => g (i.val+j.val)).det +
        S0*((Matrix.of fun i j : Fin (d+1) => f (i.val+j.val)).det/H.det)*
          u0^(e-1)*(Matrix.of fun i j : Fin (e-1) => g (i.val+j.val)).det) := by
  cases e with
  | zero => omega
  | succ e =>
    dsimp only
    convert hankel_arrow_det d e f g u t u0 hH hu using 1 <;>
      simp only [Fin.ext_iff,Fin.val_last,Nat.succ_eq_add_one,Nat.add_right_cancel_iff,
        Nat.add_sub_cancel] <;> rfl
private theorem class_zero_count (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) :
    m n ℓ 0=m0 n ℓ := by
  let s : Fin ℓ:=⟨0,(Fact.out : ℓ.Prime).pos⟩
  have h:=(class_counts n ℓ hR).2.2 s
  have ha:=congrArg Prod.fst h
  have hc:=congrArg Prod.snd h
  simp only [s,typeAC,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
  dsimp only [m,m0]
  rw [ha,hc]
  omega
private theorem class_C_key (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (hs : s.val∈Cset n ℓ) :
    s.val≠0 ∧ m n ℓ s=mC n ℓ ∧ classKey n ℓ s=keyC n ℓ := by
  have hi : r' n ℓ<s.val∧s.val≤r n ℓ:=Finset.mem_Ioc.mp hs
  have hzero : s.val≠0:=by omega
  have hlt : ¬s.val≤r' n ℓ:=by omega
  have h:=(class_counts n ℓ hR).2.2 s
  have ha:=congrArg Prod.fst h
  have hc:=congrArg Prod.snd h
  simp only [typeAC,hzero,ne_eq,not_false_eq_true,true_and,hi.2,hlt,ite_true,ite_false,Nat.add_zero] at ha hc
  have hm : m n ℓ s=mC n ℓ:=by
    unfold m mC
    rw [ha,hc]
    omega
  refine ⟨hzero,hm,?_⟩
  simp only [classKey,if_neg hzero,keyC,ha,hc,hm]

private theorem class_C_iff (n ℓ : ℕ) (s : Fin ℓ) :
    classType n ℓ s=.C ↔ s.val∈Cset n ℓ := by
  by_cases h0 : s.val=0
  · simp only [classType,h0,ite_true,Cset,Finset.mem_Ioc]
    simp
  · by_cases hr : s.val≤r n ℓ <;> by_cases hr' : s.val≤r' n ℓ <;>
      simp [classType,h0,hr,hr',Cset] <;> omega
private theorem class_key_valid (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    (classKey n ℓ s).a≤(classKey n ℓ s).c ∧ (classKey n ℓ s).c<ℓ := by
  have hc:=(class_counts n ℓ hR).1 s
  have hp:=(Fact.out : ℓ.Prime).pos
  change a n ℓ s≤c n ℓ s∧c n ℓ s<ℓ
  omega
private theorem class_C_key_valid (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (hs : s.val∈Cset n ℓ) :
    (keyC n ℓ).a≤(keyC n ℓ).c∧(keyC n ℓ).c<ℓ := by
  have hv:=class_key_valid n ℓ hR s
  rw [(class_C_key n ℓ hR s hs).2.2] at hv
  exact hv
private theorem pairRF_comm (n ℓ : ℕ) (P Q : Ix n ℓ) : pairRF n ℓ P Q=pairRF n ℓ Q P:=by
  unfold pairRF
  rw [mul_comm (crtE n ℓ P) (crtE n ℓ Q)]

private abbrev CClass (n ℓ : ℕ) := {s : Fin ℓ // s.val∈Cset n ℓ}
private def tiedSplitMap (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s0 : Fin ℓ) (hs0 : s0.val=0) :
    ((Fin (mC n ℓ) × CClass n ℓ) ⊕ Fin (m0 n ℓ)) → TiedIx n ℓ
  | .inl (i,s) => ⟨⟨s.val,⟨i.val,by
      rw [(class_C_key n ℓ hR s.val s.property).2.1]
      exact i.isLt⟩⟩,Or.inr ((class_C_iff n ℓ s.val).mpr s.property)⟩
  | .inr i => ⟨⟨s0,⟨i.val,by
      rw [hs0,class_zero_count n ℓ hR]
      exact i.isLt⟩⟩,Or.inl hs0⟩
private theorem tiedSplitMap_bijective (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s0 : Fin ℓ) (hs0 : s0.val=0) : Function.Bijective (tiedSplitMap n ℓ hR s0 hs0) := by
  constructor
  · intro x y h
    rcases x with ⟨i,s⟩|i <;> rcases y with ⟨j,t⟩|j
    · have hs : s=t := Subtype.ext (congrArg (fun P : TiedIx n ℓ => P.val.1) h)
      subst t
      have hi : i=j := Fin.ext (congrArg (fun P : TiedIx n ℓ => P.val.2.val) h)
      subst j
      rfl
    · have hs := congrArg (fun P : TiedIx n ℓ => P.val.1.val) h
      change s.val.val=s0.val at hs
      exact False.elim ((class_C_key n ℓ hR s.val s.property).1 (hs.trans hs0))
    · have hs := congrArg (fun P : TiedIx n ℓ => P.val.1.val) h
      change s0.val=t.val.val at hs
      exact False.elim ((class_C_key n ℓ hR t.val t.property).1 (hs.symm.trans hs0))
    · have hi : i=j := Fin.ext (congrArg (fun P : TiedIx n ℓ => P.val.2.val) h)
      subst j
      rfl
  · rintro ⟨⟨s,i⟩,hp⟩
    by_cases h0 : s.val=0
    · have hs : s=s0 := Fin.ext (h0.trans hs0.symm)
      subst s
      refine ⟨.inr ⟨i.val,?_⟩,?_⟩
      · rw [←class_zero_count n ℓ hR,←hs0]
        exact i.isLt
      · rfl
    · have hs : s.val∈Cset n ℓ := (class_C_iff n ℓ s).mp (hp.resolve_left h0)
      refine ⟨.inl (⟨i.val,?_⟩,⟨s,hs⟩),?_⟩
      · rw [←(class_C_key n ℓ hR s hs).2.1]
        exact i.isLt
      · rfl
private def tiedSplitEquiv (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s0 : Fin ℓ) (hs0 : s0.val=0) :
    ((Fin (mC n ℓ) × CClass n ℓ) ⊕ Fin (m0 n ℓ)) ≃ TiedIx n ℓ :=
  Equiv.ofBijective (tiedSplitMap n ℓ hR s0 hs0) (tiedSplitMap_bijective n ℓ hR s0 hs0)
private theorem class_zero_key (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s0 : Fin ℓ) (hs0 : s0.val=0) : classKey n ℓ s0=keyU n ℓ := by
  have ht := (class_counts n ℓ hR).2.2 s0
  have ha := congrArg Prod.fst ht
  have hc := congrArg Prod.snd ht
  simp only [typeAC,hs0,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
  simp only [classKey,hs0,ite_true,keyU,ha,hc,class_zero_count n ℓ hR]
private def tiedCBlock {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ) :
    Matrix (Fin (mC n ℓ) × CClass n ℓ) (Fin (mC n ℓ) × CClass n ℓ) (ZMod ℓ) :=
  Matrix.blockDiagonal fun s : CClass n ℓ => redU R s.val •
    (Matrix.of fun i j : Fin (mC n ℓ) => redMoment R (keyC n ℓ) (i.val+j.val))
private def tiedCoupling {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ) :
    Matrix (Fin (mC n ℓ) × CClass n ℓ) (Fin (m0 n ℓ)) (ZMod ℓ) :=
  fun P j => if j.val+1=m0 n ℓ then
    redU R P.2.val/(-(P.2.val.val:ZMod ℓ))*redMoment R (keyC n ℓ) (P.1.val+mC n ℓ) else 0
private def tiedZeroBlock {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ)
    (s0 : Fin ℓ) : Matrix (Fin (m0 n ℓ)) (Fin (m0 n ℓ)) (ZMod ℓ) :=
  fun i j => redU R s0*redMoment R (keyU n ℓ) (i.val+j.val) +
    if i.val+1=m0 n ℓ ∧ j.val+1=m0 n ℓ then
      S0red R*redMoment R (keyC n ℓ) (2*mC n ℓ) else 0
private theorem tied_block_split (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (R : ReductionData z n ℓ) (s0 : Fin ℓ) (hs0 : s0.val=0) :
    (tiedBlock R).submatrix (tiedSplitEquiv n ℓ hR s0 hs0) (tiedSplitEquiv n ℓ hR s0 hs0) =
      Matrix.fromBlocks (tiedCBlock R) (tiedCoupling R) (tiedCoupling R).transpose (tiedZeroBlock R s0) := by
  classical
  have hz : s0=(0:Fin ℓ) := Fin.ext hs0
  ext P Q
  rcases P with ⟨i,s⟩|i <;> rcases Q with ⟨j,t⟩|j
  · have hs := class_C_key n ℓ hR s.val s.property
    have ht := class_C_key n ℓ hR t.val t.property
    have hsne : s.val≠(0:Fin ℓ) := fun h => hs.1 (congrArg Fin.val h)
    have htne : t.val≠(0:Fin ℓ) := fun h => ht.1 (congrArg Fin.val h)
    by_cases he : s=t
    · subst t
      simp [Matrix.submatrix,tiedSplitEquiv,tiedSplitMap,tiedBlock,expectedDiagonal,
        tiedCBlock,Matrix.blockDiagonal_apply,hs.1,hsne,hs.2.2]
    · have hst : s.val≠t.val := fun h => he (Subtype.ext h)
      simp [Matrix.submatrix,tiedSplitEquiv,tiedSplitMap,tiedBlock,expectedDiagonal,
        tiedCBlock,Matrix.blockDiagonal_apply,hst,he,hs.1,ht.1,hsne,htne]
  · have hs := class_C_key n ℓ hR s.val s.property
    have hsne : s.val≠(0:Fin ℓ) := fun h => hs.1 (congrArg Fin.val h)
    have hne : s.val≠s0 := by intro h;exact hs.1 ((congrArg Fin.val h).trans hs0)
    simp [Matrix.submatrix,tiedSplitEquiv,tiedSplitMap,tiedBlock,expectedDiagonal,
      tiedCoupling,hne,s.property,hs0,hz,hsne]
  · have ht := class_C_key n ℓ hR t.val t.property
    have htne : t.val≠(0:Fin ℓ) := fun h => ht.1 (congrArg Fin.val h)
    have hne : s0≠t.val := by intro h;exact ht.1 ((congrArg Fin.val h).symm.trans hs0)
    simp [Matrix.submatrix,tiedSplitEquiv,tiedSplitMap,tiedBlock,expectedDiagonal,
      tiedCoupling,Matrix.transpose_apply,hne,t.property,hs0,hz,htne,Ne.symm htne]
  · simp [Matrix.submatrix,tiedSplitEquiv,tiedSplitMap,tiedBlock,expectedDiagonal,
      tiedZeroBlock,hs0,hz,class_zero_key n ℓ hR s0 hs0,class_zero_key n ℓ hR 0 rfl]

private theorem tied_sum_binding (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (hz : Unit ℓ (z:Padic ℓ)) (R : ReductionData z n ℓ) :
    (∑ s : CClass n ℓ, (redU R s.val/(-(s.val.val:ZMod ℓ)))^2/redU R s.val)=S0red R := by
  classical
  have he : (∑ s : CClass n ℓ, (redU R s.val/(-(s.val.val:ZMod ℓ)))^2/redU R s.val)=
      ∑ s : CClass n ℓ, redU R s.val/(s.val.val:ZMod ℓ)^2 := by
    apply Finset.sum_congr rfl
    intro s hs
    have hu := redU_ne_zero z n ℓ hz R s.val
    have hs0 := (class_C_key n ℓ hR s.val s.property).1
    have hsn : (s.val.val:ZMod ℓ)≠0 := by
      rw [ne_eq,ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) s.val.isLt
    field_simp <;> ring
  rw [he]
  exact (Finset.sum_congr_set {s : Fin ℓ | s.val∈Cset n ℓ}
    (fun s => if s.val∈Cset n ℓ then redU R s/(s.val:ZMod ℓ)^2 else 0)
    (fun s => redU R s.val/(s.val.val:ZMod ℓ)^2)
    (by intro s hs; simp only [Set.mem_setOf_eq] at hs; simp [hs])
    (by intro s hs; simp only [Set.mem_setOf_eq] at hs; simp [hs])).symm
private theorem tied_prod_binding (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) :
    (∏ s : CClass n ℓ, redU R s.val^(mC n ℓ)*redK R (keyC n ℓ))=
      ∏ s : Fin ℓ, if s.val∈Cset n ℓ then redU R s^(mC n ℓ)*redK R (keyC n ℓ) else 1 := by
  classical
  exact (Finset.prod_congr_set {s : Fin ℓ | s.val∈Cset n ℓ}
    (fun s => if s.val∈Cset n ℓ then redU R s^(mC n ℓ)*redK R (keyC n ℓ) else 1)
    (fun s => redU R s.val^(mC n ℓ)*redK R (keyC n ℓ))
    (by intro s hs; simp only [Set.mem_setOf_eq] at hs; simp [hs])
    (by intro s hs; simp only [Set.mem_setOf_eq] at hs; simp [hs])).symm
private theorem reduction_moments_eq {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A B : TypeKey)
    (ha : A.a≤A.c) (hb : B.a≤B.c) (hca : A.c<ℓ) (hcb : B.c<ℓ)
    (hw : weight A=weight B) (e : ℕ) : R.moments A e=R.moments B e := by
  apply PadicInt.ext
  rw [R.moments_cast A ha hca e,R.moments_cast B hb hcb e]
  simp only [L,hw]
private theorem redMoment_keyCplus {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (ha : (keyC n ℓ).a≤(keyC n ℓ).c)
    (hc : (keyC n ℓ).c<ℓ) (e : ℕ) :
    redMoment R (keyCplus n ℓ) e=redMoment R (keyC n ℓ) e := by
  unfold redMoment
  congr 1
  exact reduction_moments_eq R (keyCplus n ℓ) (keyC n ℓ) ha ha hc hc rfl e
private theorem redMoment_keyUminus {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (ha : (keyU n ℓ).a≤(keyU n ℓ).c)
    (hc : (keyU n ℓ).c<ℓ) (e : ℕ) :
    redMoment R (keyUminus n ℓ) e=redMoment R (keyU n ℓ) e := by
  unfold redMoment
  congr 1
  exact reduction_moments_eq R (keyUminus n ℓ) (keyU n ℓ) ha ha hc hc rfl e
private theorem class_parameters_valid (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) :
    k n ℓ < 4 ∧ (1 ≤ n/ℓ ∨ k n ℓ = 3) := by
  have hp := (Fact.out : ℓ.Prime).pos
  have hr := Nat.mod_lt n hp
  have hd := Nat.mod_add_div (4*(n%ℓ)) ℓ
  have he := Nat.mod_add_div n ℓ
  have hk : k n ℓ < 4 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  refine ⟨hk,?_⟩
  by_cases hq : 1 ≤ n/ℓ
  · exact Or.inl hq
  · right
    have hq0 : n/ℓ=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (lt_of_not_ge hq))
    have hn : n<ℓ := (Nat.div_eq_zero_iff.mp hq0).resolve_left (by omega)
    have hlarge : 3*ℓ<4*n := (hR.2.resolve_left (by omega)).2
    have hk3 : 3 ≤ k n ℓ := by
      unfold k
      rw [Nat.mod_eq_of_lt hn]
      exact (Nat.le_div_iff_mul_le hp).mpr (by omega)
    omega
private theorem class_key_mem (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) : classKey n ℓ s ∈ neededAtValid (n/ℓ) (k n ℓ) := by
  classical
  rw [neededAtValid_eq _ _ (class_parameters_valid n ℓ hR)]
  have hp := (Fact.out : ℓ.Prime).pos
  have hr := Nat.mod_lt n hp
  have hr' := Nat.mod_lt (4*(n%ℓ)) hp
  have hd := Nat.mod_add_div (4*(n%ℓ)) ℓ
  have hv := class_parameters_valid n ℓ hR
  change r' n ℓ + ℓ*k n ℓ = 4*r n ℓ at hd
  have ht := (class_counts n ℓ hR).2.2 s
  have ha := congrArg Prod.fst ht
  have hc := congrArg Prod.snd ht
  dsimp only [typeAC] at ha hc
  by_cases h0 : s.val=0
  · simp only [h0,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
    have hm : m n ℓ 0=2*(n/ℓ)+k n ℓ := by unfold m; rw [ha,hc]; omega
    simp only [classKey,h0,ite_true,ha,hc,hm,neededAt]
    by_cases hk : 1 ≤ k n ℓ
    · simp [hk]
    · have hq : 1 ≤ n/ℓ := by omega
      have hk2 : k n ℓ ≤ 2 := by omega
      simp [hk,hq,hk2]
  · by_cases hs : s.val≤r n ℓ <;> by_cases hs' : s.val≤r' n ℓ
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_true] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ-1 := by unfold m; rw [ha,hc]; omega
      simp [classKey,h0,ha,hc,hm,neededAt]
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_true,ite_false,Nat.add_zero] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ-2 := by unfold m; rw [ha,hc]; omega
      have hk : 1 ≤ k n ℓ := by
        by_contra h
        have hk0 : k n ℓ=0 := by omega
        rw [hk0,mul_zero,add_zero] at hd
        omega
      simp [classKey,h0,ha,hc,hm,neededAt,hk]
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_true,ite_false,Nat.add_zero] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ+1 := by unfold m; rw [ha,hc]; omega
      have hk : k n ℓ ≤ 2 := by
        have hr0 : r n ℓ < ℓ := hr
        have hr1 : r' n ℓ < ℓ := hr'
        by_contra h
        have hk3 : k n ℓ=3 := by omega
        rw [hk3] at hd
        omega
      have hq : 1 ≤ n/ℓ := by omega
      simp [classKey,h0,ha,hc,hm,neededAt,hq,hk]
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_false,Nat.add_zero] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ := by unfold m; rw [ha,hc]; omega
      simp [classKey,h0,ha,hc,hm,neededAt]

theorem reduction_det_tied (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (ht : tied n ℓ)
    (hK : AllConstantsUnit z (n/ℓ) (k n ℓ) ℓ)
    (R : ReductionData z n ℓ) (s0 : Fin ℓ) (hs0 : s0.val=0) :
  (tiedBlock R).det =
    (∏ s : Fin ℓ, if s.val∈Cset n ℓ then
      redU R s^(mC n ℓ)*redK R (keyC n ℓ) else 1)*
    (redU R s0^(m0 n ℓ)*redK R (keyU n ℓ) +
      S0red R*(redK R (keyCplus n ℓ)/redK R (keyC n ℓ))*
        redU R s0^(m0 n ℓ-1)*redK R (keyUminus n ℓ)) := by
  classical
  have hv := class_parameters_valid n ℓ hR
  have hm0 : 0<m0 n ℓ := by unfold m0; omega
  obtain ⟨s,hs⟩ := (class_table n ℓ hR).2.2.mp ht
  have hsi := Finset.mem_Ioc.mp hs
  let sc : Fin ℓ := ⟨s,lt_of_le_of_lt hsi.2 (Nat.mod_lt n (Fact.out : ℓ.Prime).pos)⟩
  have hsc : sc.val∈Cset n ℓ := hs
  have hCv := class_C_key_valid n ℓ hR sc hsc
  have hUv := class_key_valid n ℓ hR s0
  rw [class_zero_key n ℓ hR s0 hs0] at hUv
  have hKc : redK R (keyC n ℓ)≠0 := by
    apply redK_ne_zero z n ℓ R (keyC n ℓ) hCv.1 hCv.2
    have hh := hK (classKey n ℓ sc) (class_key_mem n ℓ hR sc)
    rwa [(class_C_key n ℓ hR sc hsc).2.2] at hh
  have hCplus : (Matrix.of fun i j : Fin (mC n ℓ+1) =>
      redMoment R (keyC n ℓ) (i.val+j.val)).det=redK R (keyCplus n ℓ) := by
    unfold redK
    change (Matrix.of fun i j : Fin (mC n ℓ+1) => redMoment R (keyC n ℓ) (i.val+j.val)).det =
      (Matrix.of fun i j : Fin (mC n ℓ+1) => redMoment R (keyCplus n ℓ) (i.val+j.val)).det
    congr 1
    ext i j
    exact (redMoment_keyCplus R hCv.1 hCv.2 _).symm
  have hUminus : (Matrix.of fun i j : Fin (m0 n ℓ-1) =>
      redMoment R (keyU n ℓ) (i.val+j.val)).det=redK R (keyUminus n ℓ) := by
    unfold redK
    change (Matrix.of fun i j : Fin (m0 n ℓ-1) => redMoment R (keyU n ℓ) (i.val+j.val)).det =
      (Matrix.of fun i j : Fin (m0 n ℓ-1) => redMoment R (keyUminus n ℓ) (i.val+j.val)).det
    congr 1
    ext i j
    exact (redMoment_keyUminus R hUv.1 hUv.2 _).symm
  have hd := hankel_arrow_det_pos (mC n ℓ) (m0 n ℓ) hm0
    (redMoment R (keyC n ℓ)) (redMoment R (keyU n ℓ))
    (fun s : CClass n ℓ => redU R s.val)
    (fun s : CClass n ℓ => redU R s.val/(-(s.val.val:ZMod ℓ))) (redU R s0)
    hKc (fun s => redU_ne_zero z n ℓ hz R s.val)
  dsimp only at hd
  rw [tied_sum_binding z n ℓ hR hz R] at hd
  change (Matrix.fromBlocks (tiedCBlock R) (tiedCoupling R) (tiedCoupling R).transpose
      (tiedZeroBlock R s0)).det =
    (∏ s : CClass n ℓ,redU R s.val^(mC n ℓ)*redK R (keyC n ℓ))*
      (redU R s0^(m0 n ℓ)*redK R (keyU n ℓ)+
        S0red R*((Matrix.of fun i j : Fin (mC n ℓ+1) => redMoment R (keyC n ℓ) (i.val+j.val)).det /
          redK R (keyC n ℓ))*redU R s0^(m0 n ℓ-1)*
            (Matrix.of fun i j : Fin (m0 n ℓ-1) => redMoment R (keyU n ℓ) (i.val+j.val)).det) at hd
  rw [hCplus,hUminus,tied_prod_binding z n ℓ R] at hd
  have hsplit := congrArg Matrix.det (tied_block_split z n ℓ hR R s0 hs0)
  rw [Matrix.det_submatrix_equiv_self] at hsplit
  exact hsplit.trans hd
#print axioms reduction_det_tied
end
end CatalanCore.Li2.NV
