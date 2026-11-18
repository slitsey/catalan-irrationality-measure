module
public import CatalanCore.Li2.NV.Reduction
public import CatalanCore.Li2.NV.Constants
public import CatalanCore.Li2.NV.Wilson
public import CatalanCore.Li2.NV.Binomial
public import CatalanCore.Li2.NV.Scale
public import Mathlib.LinearAlgebra.Matrix.Block
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators Nat
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
private def clusterLabel {ℓ : ℕ} (even p : Fin ℓ→Prop) [DecidablePred even] [DecidablePred p]
    (s : Fin ℓ) : ℕ := (if even s then 0 else ℓ+1)+(if p s then 0 else s.val+1)
private theorem clusterLabel_eq_iff {ℓ : ℕ} (even p : Fin ℓ→Prop)
    [DecidablePred even] [DecidablePred p]
    (hcluster : ∀ s t,p s→p t→(even s↔even t)) (s t : Fin ℓ) :
    clusterLabel even p s=clusterLabel even p t ↔ s=t ∨ p s∧p t := by
  constructor
  · intro h
    by_cases hs : p s <;> by_cases ht : p t
    · exact Or.inr ⟨hs,ht⟩
    · exfalso
      by_cases he : even s <;> by_cases hf : even t <;>
        simp only [clusterLabel,hs,ht,he,hf,ite_true,ite_false] at h <;> have hh:=t.isLt <;> omega
    · exfalso
      by_cases he : even s <;> by_cases hf : even t <;>
        simp only [clusterLabel,hs,ht,he,hf,ite_true,ite_false] at h <;> have hh:=s.isLt <;> omega
    · left
      apply Fin.ext
      by_cases he : even s <;> by_cases hf : even t <;>
        simp only [clusterLabel,hs,ht,he,hf,ite_true,ite_false] at h <;>
          have hh:=s.isLt <;> have hk:=t.isLt <;> omega
  · rintro (h|⟨hs,ht⟩)
    · subst t;rfl
    · simp only [clusterLabel,hs,ht,ite_true,add_zero]
      by_cases he : even s
      · have hf : even t := (hcluster s t hs ht).mp he
        simp only [he,hf,ite_true]
      · have hf : ¬even t := fun h => he ((hcluster s t hs ht).mpr h)
        simp only [he,hf,ite_false]
private theorem det_ne_zero_of_cluster {F : Type*} [CommRing F] [IsDomain F] {ℓ : ℕ}
    (m : Fin ℓ→ℕ) (even p : Fin ℓ→Prop) [DecidablePred even] [DecidablePred p]
    (hcluster : ∀ s t,p s→p t→(even s↔even t))
    (M : Matrix (Σ s,Fin (m s)) (Σ s,Fin (m s)) F)
    (hwithin : ∀ P Q,(even P.1↔even Q.1)→P.1≠Q.1→¬(p P.1∧p Q.1)→M P Q=0)
    (hBA : ∀ P Q,¬even P.1→even Q.1→M P Q=0)
    (hpdet : (M.submatrix (fun P : {P : Σ s,Fin (m s) // p P.1}=>P.val) Subtype.val).det≠0)
    (hdet : ∀ s,¬p s→(Matrix.of fun i j : Fin (m s)=>M ⟨s,i⟩ ⟨s,j⟩).det≠0) : M.det≠0 := by
  classical
  let b : (Σ s,Fin (m s))→ℕ := fun P=>clusterLabel even p P.1
  have htri : M.BlockTriangular b := by
    intro P Q hlt
    by_cases hP : even P.1 <;> by_cases hQ : even Q.1
    · apply hwithin P Q (iff_of_true hP hQ)
      · intro he
        change clusterLabel even p Q.1<clusterLabel even p P.1 at hlt
        rw [he] at hlt
        omega
      · intro hp
        have he := (clusterLabel_eq_iff even p hcluster P.1 Q.1).mpr (Or.inr hp)
        change clusterLabel even p Q.1<clusterLabel even p P.1 at hlt
        omega
    · change clusterLabel even p Q.1<clusterLabel even p P.1 at hlt
      simp only [clusterLabel,hP,hQ,ite_true,ite_false] at hlt
      have hq:=P.1.isLt
      split_ifs at hlt <;> omega
    · exact hBA P Q hP hQ
    · apply hwithin P Q (iff_of_false hP hQ)
      · intro he
        change clusterLabel even p Q.1<clusterLabel even p P.1 at hlt
        rw [he] at hlt
        omega
      · intro hp
        have he := (clusterLabel_eq_iff even p hcluster P.1 Q.1).mpr (Or.inr hp)
        change clusterLabel even p Q.1<clusterLabel even p P.1 at hlt
        omega
  rw [htri.det]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hk
  by_cases hp : p P.1
  · have he : ∀ Q : Σ s,Fin (m s), b Q=b P ↔ p Q.1 := by
      intro Q
      rw [show b Q=b P ↔ Q.1=P.1∨p Q.1∧p P.1 from clusterLabel_eq_iff even p hcluster Q.1 P.1]
      constructor
      · rintro (h|⟨h,_⟩)
        · rwa [h]
        · exact h
      · intro h;exact Or.inr ⟨h,hp⟩
    let e : {Q : Σ s,Fin (m s) // b Q=b P} ≃ {Q : Σ s,Fin (m s) // p Q.1} :=
      Equiv.subtypeEquivRight he
    have hd := Matrix.det_submatrix_equiv_self e.symm (M.toSquareBlock b (b P))
    have hn := hpdet
    simpa only [Matrix.toSquareBlock,Matrix.toSquareBlockProp,Matrix.toBlock,Matrix.submatrix,e] using
      (hd ▸ hn)
  · have he : ∀ Q : Σ s,Fin (m s), b Q=b P ↔ Q.1=P.1 := by
      intro Q
      simpa only [hp,and_false,or_false] using clusterLabel_eq_iff even p hcluster Q.1 P.1
    let e : {Q : Σ s,Fin (m s) // b Q=b P} ≃ Fin (m P.1) :=
      { toFun := fun ⟨⟨s,i⟩,h⟩ => by have hs: s=P.1:=(he ⟨s,i⟩).mp h;subst s;exact i
        invFun := fun i=>⟨⟨P.1,i⟩,rfl⟩
        left_inv := by rintro ⟨⟨s,i⟩,h⟩;have hs:s=P.1:=(he ⟨s,i⟩).mp h;subst s;rfl
        right_inv := by intro i;rfl }
    have hd : (M.toSquareBlock b (b P)).det=
        (Matrix.of fun i j : Fin (m P.1)=>M ⟨P.1,i⟩ ⟨P.1,j⟩).det :=
      (Matrix.det_submatrix_equiv_self e.symm (M.toSquareBlock b (b P))).symm
    rw [hd]
    exact hdet P.1 hp
private theorem class_C_iff (n ℓ : ℕ) (s : Fin ℓ) :
    classType n ℓ s=.C ↔ s.val∈Cset n ℓ := by
  by_cases h0 : s.val=0
  · simp only [classType,h0,ite_true,Cset,Finset.mem_Ioc]
    simp
  · by_cases hr : s.val≤r n ℓ <;> by_cases hr' : s.val≤r' n ℓ <;>
      simp [classType,h0,hr,hr',Cset] <;> omega

private theorem expectedReduction_det_ne_zero_of_tiedBlock (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (hR : Range n ℓ) (R : ReductionData z n ℓ)
    (upper : Matrix (Ix n ℓ) (Ix n ℓ) (ZMod ℓ))
    (hClass : ∀ s : Fin ℓ, redK R (classKey n ℓ s)≠0) (hTied : (tiedBlock R).det≠0) :
    (expectedReduction R upper).det≠0 := by
  classical
  let p : Fin ℓ→Prop := fun s=>s.val=0∨classType n ℓ s=.C
  have hpar : ∀ s t : Fin ℓ,p s→p t→nu n ℓ s%2=nu n ℓ t%2 := by
    intro s t hs ht
    have hps : parityGroup (classType n ℓ s)=true := by
      rcases hs with hs|hs
      · simp [classType,hs,parityGroup]
      · simp [hs,parityGroup]
    have hpt : parityGroup (classType n ℓ t)=true := by
      rcases ht with ht|ht
      · simp [classType,ht,parityGroup]
      · simp [ht,parityGroup]
    rw [(class_table n ℓ hR).1 s |>.2.2,(class_table n ℓ hR).1 t |>.2.2]
    simp only [hps,hpt,ite_true]
  have hsquare : ((expectedReduction R upper).submatrix
      (fun P : {P : Ix n ℓ // p P.1}=>P.val) Subtype.val) = tiedBlock R := by
    ext P Q
    have he := hpar P.val.1 Q.val.1 P.property Q.property
    simp only [Matrix.submatrix,expectedReduction,tiedBlock,Matrix.of_apply,he,ite_true]
  apply det_ne_zero_of_cluster (m := fun s : Fin ℓ=>m n ℓ s)
    (even := fun s=>nu n ℓ s%2=0) (p := p)
    (hcluster := fun s t hs ht => by rw [hpar s t hs ht])
    (M := expectedReduction R upper)
  · intro P Q hpq hne hnp
    have hp := Int.emod_nonneg (nu n ℓ P.1) (by norm_num : (2:ℤ)≠0)
    have hq := Int.emod_nonneg (nu n ℓ Q.1) (by norm_num : (2:ℤ)≠0)
    have hp2 := Int.emod_lt_of_pos (nu n ℓ P.1) (by norm_num : (0:ℤ)<2)
    have hq2 := Int.emod_lt_of_pos (nu n ℓ Q.1) (by norm_num : (0:ℤ)<2)
    have he : nu n ℓ P.1%2=nu n ℓ Q.1%2 := by omega
    have hl : ¬(P.1.val∈Cset n ℓ ∧ Q.1.val=0 ∧ Q.2.val+1=m0 n ℓ) := by
      rintro ⟨hC,h0,hlast⟩
      exact hnp ⟨Or.inr ((class_C_iff n ℓ P.1).mpr hC),Or.inl h0⟩
    have hr : ¬(Q.1.val∈Cset n ℓ ∧ P.1.val=0 ∧ P.2.val+1=m0 n ℓ) := by
      rintro ⟨hC,h0,hlast⟩
      exact hnp ⟨Or.inl h0,Or.inr ((class_C_iff n ℓ Q.1).mpr hC)⟩
    simp only [expectedReduction,he,ite_true,expectedDiagonal,if_neg hne,if_neg hl,if_neg hr]
  · intro P Q hp hq
    have he : nu n ℓ P.1%2≠nu n ℓ Q.1%2 := by omega
    simp only [expectedReduction,if_neg he,if_neg hp]
  · rw [hsquare]
    exact hTied
  · intro s hs
    have hs0 : s.val≠0 := fun h=>hs (Or.inl h)
    have hse : s≠(0:Fin ℓ) := fun h=>hs0 (congrArg Fin.val h)
    have he : (Matrix.of fun i j : Fin (m n ℓ s)=>expectedReduction R upper ⟨s,i⟩ ⟨s,j⟩)=
        redU R s • (Matrix.of fun i j : Fin (m n ℓ s)=>redMoment R (classKey n ℓ s) (i.val+j.val)) := by
      ext i j
      simp [expectedReduction,expectedDiagonal,hs0,hse]
    rw [he,Matrix.det_smul,Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ (redU_ne_zero z n ℓ hz R s)) (hClass s)
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
private theorem class_zero_key (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s0 : Fin ℓ) (hs0 : s0.val=0) : classKey n ℓ s0=keyU n ℓ := by
  have ht := (class_counts n ℓ hR).2.2 s0
  have ha := congrArg Prod.fst ht
  have hc := congrArg Prod.snd ht
  simp only [typeAC,hs0,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
  simp only [classKey,hs0,ite_true,keyU,ha,hc,class_zero_count n ℓ hR]
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
private def invNatLoc (ℓ m : ℕ) [Fact ℓ.Prime] : Basic.LocRing ℓ :=
  if h : ¬ℓ∣m then ⟨(m:ℚ)⁻¹,Basic.inv_natCast_mem_locRing h⟩ else 0
private theorem invNatLoc_cast (ℓ m : ℕ) [Fact ℓ.Prime] (hm : ¬ℓ∣m) :
    (invNatLoc ℓ m:ℚ)=(m:ℚ)⁻¹ := by simp only [invNatLoc,dif_pos hm]
private theorem invNatLoc_red (ℓ m : ℕ) [Fact ℓ.Prime] :
    Arith.Hybrid.redQ ℓ (invNatLoc ℓ m)=(m:ZMod ℓ)⁻¹ := by
  classical
  by_cases hm : ℓ∣m
  · have he : (m:ZMod ℓ)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hm
    simp [invNatLoc,hm,he]
  · have hm0 : m≠0 := by intro h;subst m;exact hm (dvd_zero _)
    have he : (m:Basic.LocRing ℓ)*invNatLoc ℓ m=1 := by
      apply Subtype.ext
      change (m:ℚ)*(invNatLoc ℓ m:ℚ)=1
      rw [invNatLoc_cast ℓ m hm]
      exact mul_inv_cancel₀ (by exact_mod_cast hm0)
    have hh := congrArg (Arith.Hybrid.redQ ℓ) he
    simp only [map_mul,map_natCast,map_one] at hh
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hh)
private theorem fact_not_dvd (ℓ m : ℕ) [Fact ℓ.Prime] (hm : m<ℓ) : ¬ℓ∣m.factorial := by
  rw [←ZMod.natCast_eq_zero_iff]
  rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [ne_eq,ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by have hh:=Finset.mem_range.mp hi;omega)
private theorem binomial_tail_mod (ℓ r t : ℕ) [Fact ℓ.Prime] (ht : t<r) (hr : r<ℓ)
    (y : ZMod ℓ) :
    BinTail r t y=(r.factorial:ZMod ℓ)/((t.factorial:ZMod ℓ)*((r-t-1).factorial:ZMod ℓ))*
      ∑ j∈Finset.range (r-t),(-1:ZMod ℓ)^j*(Nat.choose (r-t-1) j:ZMod ℓ)/(t+1+j:ZMod ℓ)*y^(t+1+j) := by
  classical
  let Y : Basic.LocRing ℓ := (y.val:ℕ)
  let L : Basic.LocRing ℓ := ∑ i∈Finset.Ioc t r,(Nat.choose r i:Basic.LocRing ℓ)*Y^i*(1-Y)^(r-i)
  let R : Basic.LocRing ℓ :=
    (r.factorial:Basic.LocRing ℓ)*invNatLoc ℓ t.factorial*invNatLoc ℓ (r-t-1).factorial *
      ∑ j∈Finset.range (r-t),(-1:Basic.LocRing ℓ)^j*(Nat.choose (r-t-1) j:Basic.LocRing ℓ)*
        invNatLoc ℓ (t+1+j)*Y^(t+1+j)
  have hL : (L:ℚ)=BinTail r t (Y:ℚ) := by
    change (Basic.LocRing ℓ).subtype L=_
    simp only [L,BinTail,map_sum,map_mul,map_pow,map_sub,map_one,map_natCast,Subring.subtype_apply]
  have hR : (R:ℚ)=
      (r.factorial:ℚ)/((t.factorial:ℚ)*((r-t-1).factorial:ℚ))*
        ∑ j∈Finset.range (r-t),(-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ)/(t+1+j:ℚ)*(Y:ℚ)^(t+1+j) := by
    change (Basic.LocRing ℓ).subtype R=_
    simp only [R,map_mul,map_sum,map_pow,map_natCast,map_neg,map_one,Subring.subtype_apply,
      invNatLoc_cast ℓ t.factorial (fact_not_dvd ℓ t (by omega)),
      invNatLoc_cast ℓ (r-t-1).factorial (fact_not_dvd ℓ (r-t-1) (by omega)),
      div_eq_mul_inv,_root_.mul_inv_rev]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [invNatLoc_cast ℓ (t+1+j)
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
      simp only [Nat.cast_add,Nat.cast_one]
  have hLR : L=R := by
    apply Subtype.ext
    rw [hL,hR]
    have hh := congrArg (fun P : ℚ[X] => P.eval (Y:ℚ)) (binomial_tail_identity r t ht)
    simpa only [Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_sub,Polynomial.eval_one,BinTail] using hh
  have hh := congrArg (Arith.Hybrid.redQ ℓ) hLR
  simpa only [L,R,map_sum,map_mul,map_pow,map_sub,map_neg,map_one,map_natCast,invNatLoc_red,Y,
    ZMod.natCast_zmod_val,BinTail,div_eq_mul_inv,_root_.mul_inv_rev,
    Nat.cast_add,Nat.cast_one,mul_comm,mul_left_comm,mul_assoc] using hh

private theorem binomial_wilson_term (ℓ r t β j : ℕ) [Fact ℓ.Prime]
    (ht : t<r) (hr : r<ℓ) (hj : j<r-t) (x : ZMod ℓ) :
    (-(t+1+j:ZMod ℓ)*x^(-((t+1+j:ℕ):ℤ))*(-1:ZMod ℓ)^(β+j)/
      ((j.factorial:ZMod ℓ)*((r-t-1-j).factorial:ZMod ℓ)))/(t+1+j:ZMod ℓ)^2 =
    -((-1:ZMod ℓ)^β*(t.factorial:ZMod ℓ)/(r.factorial:ZMod ℓ))*
      ((r.factorial:ZMod ℓ)/((t.factorial:ZMod ℓ)*((r-t-1).factorial:ZMod ℓ)))*
      ((-1:ZMod ℓ)^j*(Nat.choose (r-t-1) j:ZMod ℓ)/(t+1+j:ZMod ℓ)*(x⁻¹)^(t+1+j)) := by
  have hNj : j≤r-t-1 := by omega
  have hchoose : (Nat.choose (r-t-1) j:ZMod ℓ)*
      (j.factorial:ZMod ℓ)*((r-t-1-j).factorial:ZMod ℓ)=((r-t-1).factorial:ZMod ℓ) := by
    simpa only [Nat.cast_mul] using congrArg (fun k : ℕ=>(k:ZMod ℓ))
      (Nat.choose_mul_factorial_mul_factorial hNj)
  have hn (d : ℕ) (hd : d<ℓ) : (d.factorial:ZMod ℓ)≠0 := by
    rw [ne_eq,ZMod.natCast_eq_zero_iff]
    exact fact_not_dvd ℓ d hd
  have hN := hn (r-t-1) (by omega)
  have hJ := hn j (by omega)
  have hK := hn (r-t-1-j) (by omega)
  have hT := hn t (by omega)
  have hR := hn r hr
  have hs : (t+1+j:ZMod ℓ)≠0 := by
    rw [show (t+1+j:ZMod ℓ)=((t+1+j:ℕ):ZMod ℓ) by simp,ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hc : (Nat.choose (r-t-1) j:ZMod ℓ)=
      ((r-t-1).factorial:ZMod ℓ)/((j.factorial:ZMod ℓ)*((r-t-1-j).factorial:ZMod ℓ)) := by
    apply (eq_div_iff (mul_ne_zero hJ hK)).mpr
    simpa only [mul_assoc] using hchoose
  rw [hc]
  simp only [_root_.zpow_neg,zpow_natCast,inv_pow,pow_add]
  field_simp <;> ring
private theorem S0_binomial (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (hR : Range n ℓ) (ht : tied n ℓ)
    (R : ReductionData z n ℓ) (s0 : Fin ℓ) (hs0 : s0.val=0) :
    S0red R / redU R s0 = -BinTail (r n ℓ) (r' n ℓ) (reduceInt ℓ (zInteger z ℓ hz))⁻¹ := by
  classical
  let r0 := r n ℓ
  let t0 := r' n ℓ
  let β := 3*(n/ℓ)+k n ℓ
  let x := reduceInt ℓ (zInteger z ℓ hz)
  have htr : t0<r0 := ht
  have hr : r0<ℓ := Nat.mod_lt n (Fact.out : ℓ.Prime).pos
  let f : ℕ→ZMod ℓ := fun j =>
    (-(t0+1+j:ZMod ℓ)*x^(-((t0+1+j:ℕ):ℤ))*(-1:ZMod ℓ)^(β+j)/
      ((j.factorial:ZMod ℓ)*((r0-t0-1-j).factorial:ZMod ℓ)))/(t0+1+j:ZMod ℓ)^2
  have hsum : S0red R=∑ j∈Finset.range (r0-t0),f j := by
    rw [S0red,←Finset.sum_filter]
    refine Finset.sum_bij (fun s hs=>s.val-t0-1) ?_ ?_ ?_ ?_
    · intro s hs
      have hh := Finset.mem_Ioc.mp (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_range]
      change t0<s.val∧s.val≤r0 at hh
      omega
    · intro s hs t ht he
      have hs' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hs).2
      have ht' := Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).2
      change t0<s.val∧s.val≤r0 at hs'
      change t0<t.val∧t.val≤r0 at ht'
      apply Fin.ext
      omega
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      let s : Fin ℓ := ⟨t0+1+j,by omega⟩
      refine ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact Finset.mem_Ioc.mpr ⟨by dsimp [s];omega,by dsimp [s];omega⟩
      · dsimp [s];omega
    · intro s hs
      have hh := Finset.mem_Ioc.mp (Finset.mem_filter.mp hs).2
      change t0<s.val∧s.val≤r0 at hh
      let j := s.val-t0-1
      have hsj : s.val=t0+1+j := by dsimp [j];omega
      have hj : j≤r0-t0-1 := by dsimp [j];omega
      have hw := (wilson_constants z n ℓ hz hR ht R s0 hs0).2 s j hsj hj
      rw [hw]
      change _=f j
      simp only [f,←hsj]
      have hcast : (s.val:ZMod ℓ)=(t0:ZMod ℓ)+1+j := by
        simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun k : ℕ=>(k:ZMod ℓ)) hsj
      rw [←hcast]
  have hw0 := (wilson_constants z n ℓ hz hR ht R s0 hs0).1
  have hterms : ∀ j∈Finset.range (r0-t0), f j =
      -redU R s0*((r0.factorial:ZMod ℓ)/((t0.factorial:ZMod ℓ)*((r0-t0-1).factorial:ZMod ℓ)))*
      ((-1:ZMod ℓ)^j*(Nat.choose (r0-t0-1) j:ZMod ℓ)/(t0+1+j:ZMod ℓ)*(x⁻¹)^(t0+1+j)) := by
    intro j hj
    rw [hw0]
    exact binomial_wilson_term ℓ r0 t0 β j htr hr (Finset.mem_range.mp hj) x
  have hb := binomial_tail_mod ℓ r0 t0 htr hr x⁻¹
  rw [hsum,Finset.sum_congr rfl hterms,←Finset.mul_sum,mul_assoc,←hb]
  rw [neg_mul,neg_div,mul_div_cancel_left₀ _ (redU_ne_zero z n ℓ hz R s0)]
private theorem evals_nonzero_of_gram (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (x : ℚ) (hG : (G z n ℓ x).det≠0) :
    (rawQ z n).eval x≠0 ∧ (li2Family z).evalQ n x≠0 ∧ (primitiveFamily z).evalQ n x≠0 := by
  classical
  have hc : Fintype.card (Ix n ℓ)=2*n := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using (class_counts n ℓ hR).2.1
  let e : Ix n ℓ≃Fin (2*n) := Fintype.equivFinOfCardEq hc
  have hb := crt_gram_bridge z x n ℓ hR e
  have hQ : (rawQ z n).eval x≠0 := by
    intro he
    apply hG
    have hd : (G z n ℓ x).det=((crtT n ℓ e).det:ℚ)^2*(rawQ z n).eval x := hb.2.1
    rw [hd,he,mul_zero]
  have hh := evalQ_eq_hankel z x n
  refine ⟨hQ,?_,?_⟩
  · rw [hh.2.1]
    exact mul_ne_zero hh.2.2.2.2.ne' hQ
  · rw [hh.2.2.1]
    exact mul_ne_zero hh.2.2.2.1.ne' hQ

private theorem all_class_redK_nonzero (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (hK : AllConstantsUnit z (n/ℓ) (k n ℓ) ℓ)
    (R : ReductionData z n ℓ) : ∀ s : Fin ℓ,redK R (classKey n ℓ s)≠0 := by
  intro s
  have hc := class_key_valid n ℓ hR s
  exact redK_ne_zero z n ℓ R (classKey n ℓ s) hc.1 hc.2 (hK _ (class_key_mem n ℓ hR s))
private theorem tied_block_det_ne_zero (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (ht : tied n ℓ) (hK : AllConstantsUnit z (n/ℓ) (k n ℓ) ℓ)
    (hT : Unit ℓ (Tprime z n ℓ:Padic ℓ)) (R : ReductionData z n ℓ) : (tiedBlock R).det≠0 := by
  classical
  let s0 : Fin ℓ := ⟨0,(Fact.out : ℓ.Prime).pos⟩
  have hs0 : s0.val=0 := rfl
  have hu := redU_ne_zero z n ℓ hz R s0
  have hclass := all_class_redK_nonzero z n ℓ hR hK R
  obtain ⟨s,hs⟩ := (class_table n ℓ hR).2.2.mp ht
  have hsi := Finset.mem_Ioc.mp hs
  let sc : Fin ℓ := ⟨s,lt_of_le_of_lt hsi.2 (Nat.mod_lt n (Fact.out : ℓ.Prime).pos)⟩
  have hsc : sc.val∈Cset n ℓ := hs
  have hCv := class_C_key_valid n ℓ hR sc hsc
  have hUv := class_key_valid n ℓ hR s0
  rw [class_zero_key n ℓ hR s0 hs0] at hUv
  have hkc : redK R (keyC n ℓ)≠0 := by
    have hh := hclass sc
    rwa [(class_C_key n ℓ hR sc hsc).2.2] at hh
  have hv := class_parameters_valid n ℓ hR
  have hm0 : 2≤m0 n ℓ := by unfold m0;omega
  have hD : redK R (keyU n ℓ)*redK R (keyC n ℓ)-
      redK R (keyUminus n ℓ)*redK R (keyCplus n ℓ)*
        BinTail (r n ℓ) (r' n ℓ) (reduceInt ℓ (zInteger z ℓ hz))⁻¹≠0 := by
    have hh := (Tprime_unit_iff R hz hm0 hCv.1 hCv.2 hUv.1 hUv.2).mp hT
    rwa [TprimeInt_red] at hh
  have hS : S0red R= -redU R s0*BinTail (r n ℓ) (r' n ℓ) (reduceInt ℓ (zInteger z ℓ hz))⁻¹ := by
    have hh := (div_eq_iff hu).mp (S0_binomial z n ℓ hz hR ht R s0 hs0)
    rw [hh]
    ring
  have hpow : redU R s0^(m0 n ℓ)=redU R s0^(m0 n ℓ-1)*redU R s0 := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤m0 n ℓ)]
  have hbracket : redU R s0^(m0 n ℓ)*redK R (keyU n ℓ)+
      S0red R*(redK R (keyCplus n ℓ)/redK R (keyC n ℓ))*redU R s0^(m0 n ℓ-1)*redK R (keyUminus n ℓ) =
      (redU R s0^(m0 n ℓ)/redK R (keyC n ℓ))*
        (redK R (keyU n ℓ)*redK R (keyC n ℓ)-
          redK R (keyUminus n ℓ)*redK R (keyCplus n ℓ)*
            BinTail (r n ℓ) (r' n ℓ) (reduceInt ℓ (zInteger z ℓ hz))⁻¹) := by
    rw [hS,hpow]
    field_simp <;> ring
  rw [reduction_det_tied z n ℓ hz h1 hR ht hK R s0 hs0]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    split_ifs
    · exact mul_ne_zero (pow_ne_zero _ (redU_ne_zero z n ℓ hz R s)) hkc
    · exact one_ne_zero
  · rw [hbracket]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hu) hkc) hD
theorem pointwise_nv (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (hK : AllConstantsUnit z (n/ℓ) (k n ℓ) ℓ)
    (ht : tied n ℓ → Unit ℓ (Tprime z n ℓ:Padic ℓ)) :
  ∀ x : ℚ, Vge ℓ (x:Padic ℓ) (-1) →
    (rawQ z n).eval x≠0 ∧ (li2Family z).evalQ n x≠0 ∧ (primitiveFamily z).evalQ n x≠0 := by
  intro x hx
  obtain ⟨R,upper,Ξ,ex,ey,Z,hE,hscale,hred⟩ := scaled_gram_reduction z x n ℓ hz h1 hR hx
  have hn : (expectedReduction R upper).det≠0 := by
    by_cases hTie : tied n ℓ
    · exact expectedReduction_det_ne_zero_of_tiedBlock z n ℓ hz hR R upper
        (all_class_redK_nonzero z n ℓ hR hK R) (tied_block_det_ne_zero z n ℓ hz h1 hR hTie hK (ht hTie) R)
    · exact (reduction_det_tiefree z n ℓ hz h1 hR hTie hK R upper).2
  have hG : (G z n ℓ x).det≠0 :=
    det_ne_zero_of_scaled_reduction ℓ (G z n ℓ x) Z (2*Ξ) ex ey hscale (by rw [hred];exact hn)
  exact evals_nonzero_of_gram z n ℓ hR x hG
#print axioms pointwise_nv
end
end CatalanCore.Li2.NV
