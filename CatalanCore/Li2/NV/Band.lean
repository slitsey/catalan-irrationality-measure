module
public import CatalanCore.Li2.NV.Pointwise
public import CatalanCore.Li2.NV.Pairs
public import CatalanCore.Li2.NV.PairPolynomial
public import CatalanCore.Measure.BandNV
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
private theorem rat_unit_outside_support (z : ℚ) (hz : z≠0) (ℓ : ℕ) [Fact ℓ.Prime]
    (hnot : ℓ∉Port.Li2.ratPrimeSupport z) : Unit ℓ (z:Padic ℓ) := by
  rw [Unit,Padic.eq_padicNorm,padicNorm.eq_zpow_of_nonzero hz,
    Port.Li2.padicValRat_eq_zero_of_not_mem_ratPrimeSupport (Fact.out : ℓ.Prime) hnot]
  norm_num
private theorem neededAtValid_subset_needed (q0 q k : ℕ) (hq : q≤q0)
    (hv : k<4 ∧ (1≤q∨k=3)) : neededAtValid q k ⊆ needed q0 := by
  classical
  rw [neededAtValid_eq q k hv]
  intro A hA
  apply Finset.mem_biUnion.mpr
  refine ⟨q,Finset.mem_range.mpr (by omega),?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k,?_,hA⟩
  by_cases hq0 : q=0
  · have hk : k=3 := by omega
    simp only [hq0,ite_true,Finset.mem_singleton,hk]
  · simp only [hq0,ite_false,Finset.mem_range]
    exact hv.1
private theorem exists_bad_unit_constants (z : ℚ) (q0 : ℕ) (hK : AllConstantsNonzero z q0) :
    ∃ bad : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ∉bad → ∀ q k : ℕ,
      q≤q0 → (k<4 ∧ (1≤q∨k=3)) → AllConstantsUnit z q k ℓ := by
  classical
  refine ⟨(needed q0).biUnion (fun A=>Port.Li2.ratPrimeSupport (K A z)),?_⟩
  intro ℓ inst hnot q k hq hv A hA
  have hAN := neededAtValid_subset_needed q0 q k hq hv hA
  apply rat_unit_outside_support (K A z) (hK A hAN) ℓ
  intro he
  exact hnot (Finset.mem_biUnion.mpr ⟨A,hAN,he⟩)
private theorem rational_argument_Vge (ℓ : ℕ) [Fact ℓ.Prime] (p : ℤ) (q : ℕ)
    (hq : 0<q) (hno : ¬ℓ^2∣q) : Vge ℓ (((p:ℚ)/q:ℚ):Padic ℓ) (-1) := by
  by_cases hp : p=0
  · simp only [hp,Int.cast_zero,zero_div,Rat.cast_zero,Vge,norm_zero]
    positivity
  · have hq0 : (q:ℚ)≠0 := by exact_mod_cast hq.ne'
    have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp
    have hval : padicValNat ℓ q<2 := by
      apply lt_of_not_ge
      intro he
      exact hno ((Nat.pow_dvd_iff_le_padicValNat (Fact.out : ℓ.Prime).ne_one hq.ne').mpr he)
    have hv : (-1:ℤ)≤padicValRat ℓ ((p:ℚ)/q) := by
      rw [padicValRat.div hp0 hq0,padicValRat.of_int,padicValRat.of_nat]
      omega
    have hVG : Port.Li2.VG ℓ ((p:ℚ)/q) (-1) := Or.inr (by exact_mod_cast hv)
    have hn := (Port.Li2.VG_iff_padic_norm_le ((p:ℚ)/q) (-1)).mp hVG
    simpa only [Vge,Int.cast_neg,Int.cast_one,Rat.cast_neg,Rat.cast_one] using hn
private theorem band_range_parameters (q0 n ℓ : ℕ)
    (hn : (4*(q0+1)+13)*(q0+1)≤n)
    (ha : 1/((q0:ℝ)+1)*((n:ℝ)+1)<ℓ) (hb : (ℓ:ℝ)<(4/3:ℝ)*n) :
    13≤ℓ ∧ Range n ℓ ∧ Range (n+1) ℓ ∧ n/ℓ≤q0 ∧ (n+1)/ℓ≤q0 := by
  have hd : 0<(q0:ℝ)+1 := by positivity
  have hprod : (n:ℝ)+1<((q0:ℝ)+1)*(ℓ:ℝ) := by
    rw [show 1/((q0:ℝ)+1)*((n:ℝ)+1)=((n:ℝ)+1)/((q0:ℝ)+1) by ring,
      div_lt_iff₀ hd] at ha
    nlinarith
  have hNat : n+1<(q0+1)*ℓ := by exact_mod_cast hprod
  have hm : (4*(q0+1)+13)*(q0+1)<ℓ*(q0+1) := by nlinarith [hn,hNat]
  have hl : 4*(q0+1)+13<ℓ := (Nat.mul_lt_mul_right (by omega : 0<q0+1)).mp hm
  have hp : 0<ℓ := by omega
  have h4 : 4*(n+1)<ℓ*(ℓ-1) := by
    have hi : 4*(q0+1)<ℓ-1 := by omega
    have hm := Nat.mul_lt_mul_of_pos_left hi hp
    nlinarith [hNat]
  have hband : 3*ℓ<4*n := by exact_mod_cast (show 3*(ℓ:ℝ)<4*(n:ℝ) by nlinarith [hb])
  have hR : Range n ℓ := by
    refine ⟨by omega,?_⟩
    by_cases h : ℓ≤n
    · exact Or.inl h
    · exact Or.inr ⟨by omega,hband⟩
  have hR1 : Range (n+1) ℓ := by
    refine ⟨h4,?_⟩
    by_cases h : ℓ≤n+1
    · exact Or.inl h
    · exact Or.inr ⟨by omega,by omega⟩
  have hq0 : n/ℓ<q0+1 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hq1 : (n+1)/ℓ<q0+1 := (Nat.div_lt_iff_lt_mul hp).mpr hNat
  exact ⟨by omega,hR,hR1,Nat.lt_succ_iff.mp hq0,Nat.lt_succ_iff.mp hq1⟩
private theorem pairPoly_map {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) (y : R) :
    (pairPoly y).map f=pairPoly (f y) := by
  simp only [pairPoly,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,
    Polynomial.map_X,Polynomial.map_sub,Polynomial.map_neg,Polynomial.map_natCast,Polynomial.map_ofNat,
    map_add,map_sub,map_mul,map_pow,map_neg,map_natCast,map_ofNat]
private theorem clearDen_integral_lift (ℓ : ℕ) [Fact ℓ.Prime] (P : ℚ[X]) (M : (PadicInt ℓ)[X])
    (hcast : M.map PadicInt.Coe.ringHom=P.map (Rat.castHom (Padic ℓ))) :
    (clearDen P).map (Int.castRingHom (PadicInt ℓ))=C (coeffDen P:PadicInt ℓ)*M := by
  have hf : Function.Injective (PadicInt.Coe.ringHom : PadicInt ℓ→+*Padic ℓ) := by
    intro a b h
    exact PadicInt.ext h
  apply Polynomial.map_injective (f:=PadicInt.Coe.ringHom) hf
  have hc : PadicInt.Coe.ringHom.comp (Int.castRingHom (PadicInt ℓ))=
      (Rat.castHom (Padic ℓ)).comp (Int.castRingHom ℚ) := by
    ext z
    simp only [RingHom.comp_apply,map_intCast,Int.coe_castRingHom]
  have he : ((clearDen P).map (Int.castRingHom (PadicInt ℓ))).map PadicInt.Coe.ringHom=
      ((clearDen P).map (Int.castRingHom ℚ)).map (Rat.castHom (Padic ℓ)) := by
    rw [Polynomial.map_map,Polynomial.map_map,hc]
  rw [he,(clearDen_spec P).2]
  simp only [Polynomial.map_mul,Polynomial.map_C,hcast,map_natCast,Polynomial.map_natCast]
private theorem cleared_pair_root (ℓ : ℕ) [Fact ℓ.Prime] (y : ℚ) (yi : PadicInt ℓ)
    (hyi : (yi:Padic ℓ)=(y:Padic ℓ)) (x : ZMod ℓ)
    (hroot : (pairPoly (reduceInt ℓ yi)).eval x=0) :
    ((clearDen (pairPoly y)).map (Int.castRingHom (ZMod ℓ))).eval x=0 := by
  have hcast : (pairPoly yi).map PadicInt.Coe.ringHom=
      (pairPoly y).map (Rat.castHom (Padic ℓ)) := by
    rw [pairPoly_map,pairPoly_map]
    exact congrArg pairPoly hyi
  have hl := clearDen_integral_lift ℓ (pairPoly y) (pairPoly yi) hcast
  have he := congrArg (Polynomial.map (reduceInt ℓ)) hl
  simp only [Polynomial.map_map,Polynomial.map_mul,Polynomial.map_C,pairPoly_map,map_natCast] at he
  have hc : (reduceInt ℓ).comp (Int.castRingHom (PadicInt ℓ))=Int.castRingHom (ZMod ℓ) := by
    ext z
    simp only [RingHom.comp_apply,map_intCast,Int.coe_castRingHom]
  rw [hc] at he
  rw [he]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,hroot,mul_zero]
private theorem coe_inv_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) (hx : ‖x‖=1) :
    ((x.inv:PadicInt ℓ):Padic ℓ)=(x:Padic ℓ)⁻¹ := by
  have hm:=congrArg (fun y : PadicInt ℓ=>(y:Padic ℓ)) (PadicInt.mul_inv hx)
  simp only [PadicInt.coe_mul,PadicInt.coe_one] at hm
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)
private theorem reduce_inv_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) (hx : ‖x‖=1) :
    reduceInt ℓ x.inv=(reduceInt ℓ x)⁻¹ := by
  have hm:=congrArg (reduceInt ℓ) (PadicInt.mul_inv hx)
  simp only [map_mul,map_one] at hm
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)

private theorem exists_pair_residues (z : ℚ) (hz : z≠0) :
    ∃ (bad : Finset ℕ) (res : ℕ→Finset ℕ), (∀ ℓ,(res ℓ).card≤3) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ∉bad → ∀ (hzu : Unit ℓ (z:Padic ℓ)) (n : ℕ),
        (pairPoly (reduceInt ℓ (zInteger z ℓ hzu))⁻¹).eval (n:ZMod ℓ)=0 → n%ℓ∈res ℓ := by
  classical
  obtain ⟨bad,hbad⟩ := (pair_poly_nonzero z⁻¹ (inv_ne_zero hz)).2.2
  let G (ℓ : ℕ) : (ZMod ℓ)[X] := (clearDen (pairPoly z⁻¹)).map (Int.castRingHom (ZMod ℓ))
  let res : ℕ→Finset ℕ := fun ℓ => if h : ℓ.Prime ∧ ℓ∉bad then by
    letI : Fact ℓ.Prime := ⟨h.1⟩
    exact (G ℓ).roots.toFinset.image ZMod.val
    else ∅
  refine ⟨bad,res,?_,?_⟩
  · intro ℓ
    by_cases h : ℓ.Prime ∧ ℓ∉bad
    · letI : Fact ℓ.Prime := ⟨h.1⟩
      simp only [res,dif_pos h]
      exact (Finset.card_image_le).trans (hbad ℓ h.2).2.2
    · simp only [res,dif_neg h,Finset.card_empty]
      omega
  · intro ℓ inst hnot hzu n hn
    have hg : G ℓ≠0 := (hbad ℓ hnot).2.1
    have hgood : ℓ.Prime∧ℓ∉bad := ⟨Fact.out,hnot⟩
    have hyi : ((zInteger z ℓ hzu).inv:Padic ℓ)=((z⁻¹:ℚ):Padic ℓ) := by
      rw [coe_inv_of_unit ℓ _ (show ‖zInteger z ℓ hzu‖=1 from hzu)]
      simp only [zInteger,Rat.cast_inv]
    have hroot : (G ℓ).eval (n:ZMod ℓ)=0 := by
      apply cleared_pair_root ℓ z⁻¹ (zInteger z ℓ hzu).inv hyi (n:ZMod ℓ)
      rwa [reduce_inv_of_unit ℓ _ (show ‖zInteger z ℓ hzu‖=1 from hzu)]
    have hm : (n:ZMod ℓ)∈(G ℓ).roots.toFinset := by
      rw [Multiset.mem_toFinset,Polynomial.mem_roots hg]
      exact hroot
    simp only [res,dif_pos hgood]
    exact Finset.mem_image.mpr ⟨(n:ZMod ℓ),hm,by simp only [ZMod.val_natCast]⟩
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

private theorem Tprime_Vge_of_not_unit (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (hR : Range n ℓ)
    (hnot : ¬Unit ℓ (Tprime z n ℓ:Padic ℓ)) : Vge ℓ (Tprime z n ℓ:Padic ℓ) 1 := by
  classical
  let R : ReductionData z n ℓ := Classical.choice (reduction_data_exists z n ℓ hz h1)
  let s0 : Fin ℓ := ⟨0,(Fact.out : ℓ.Prime).pos⟩
  have ht := (class_counts n ℓ hR).2.2 s0
  have ha := congrArg Prod.fst ht
  have hc := congrArg Prod.snd ht
  simp only [s0,typeAC,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
  have hb := (class_counts n ℓ hR).1 s0
  have hv := class_parameters_valid n ℓ hR
  have hm0 : 2≤m0 n ℓ := by unfold m0;omega
  have hCv : (keyC n ℓ).a≤(keyC n ℓ).c ∧ (keyC n ℓ).c<ℓ := by
    change n/ℓ+1≤4*(n/ℓ)+k n ℓ ∧ 4*(n/ℓ)+k n ℓ<ℓ
    dsimp only [s0] at ha hc hb
    rw [ha,hc] at hb
    have hp := (Fact.out : ℓ.Prime).pos
    omega
  have hUv : (keyU n ℓ).a≤(keyU n ℓ).c ∧ (keyU n ℓ).c<ℓ := by
    change n/ℓ≤4*(n/ℓ)+k n ℓ ∧ 4*(n/ℓ)+k n ℓ<ℓ
    exact ⟨by omega,hCv.2⟩
  have hcast := TprimeInt_cast R hz hm0 hCv.1 hCv.2 hUv.1 hUv.2
  have hlt : ‖TprimeInt R hz‖<1 := by
    apply lt_of_le_of_ne (PadicInt.norm_le_one _)
    intro he
    apply hnot
    rw [←hcast]
    exact he
  have hn : ‖TprimeInt R hz‖≤(ℓ:ℝ)^(-1:ℤ) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one _ (-1)).mpr (by simpa using hlt)
  have hn' : ‖(Tprime z n ℓ:Padic ℓ)‖≤(ℓ:ℝ)⁻¹ := by
    rw [←hcast]
    simpa only [PadicInt.norm_def,_root_.zpow_neg,zpow_one] using hn
  simpa only [Vge,Int.cast_one,Real.rpow_neg_one] using hn'

private theorem tied_k_pos (n ℓ : ℕ) (ht : tied n ℓ) : 1≤k n ℓ := by
  have hd : r' n ℓ+ℓ*k n ℓ=4*r n ℓ := Nat.mod_add_div (4*(n%ℓ)) ℓ
  by_contra h
  have hk : k n ℓ=0 := by omega
  rw [hk,mul_zero,add_zero] at hd
  unfold tied at ht
  omega
theorem bandNV_li2 (z : ℚ) (hz : z≠0) (h1 : z≠1) (q0 : ℕ)
    (hK : AllConstantsNonzero z q0) :
    Nonempty (CatalanCore.Measure.BandNV (primitiveFamily z) id (1/((q0:ℝ)+1)) (4/3)) := by
  classical
  obtain ⟨badK,hbadK⟩ := exists_bad_unit_constants z q0 hK
  obtain ⟨badP,res,hres,hResid⟩ := exists_pair_residues z hz
  let bad := badK ∪ (badP ∪ (Port.Li2.ratPrimeSupport z ∪ Port.Li2.ratPrimeSupport (1-z)))
  refine ⟨{ bad:=bad, res:=res, res_card:=hres, n0:=(4*(q0+1)+13)*(q0+1), nv:=?_ }⟩
  intro ℓ n hprime hnot hn ha hb hresnot p q hq hno
  letI : Fact ℓ.Prime := ⟨hprime⟩
  have hparts : ℓ∉badK ∧ ℓ∉badP ∧ ℓ∉Port.Li2.ratPrimeSupport z ∧ ℓ∉Port.Li2.ratPrimeSupport (1-z) := by
    simpa only [bad,Finset.mem_union,not_or] using hnot
  have hzu := rat_unit_outside_support z hz ℓ hparts.2.2.1
  have h1u := rat_unit_outside_support (1-z) (sub_ne_zero.mpr (Ne.symm h1)) ℓ hparts.2.2.2
  have hr := band_range_parameters q0 n ℓ hn ha hb
  have hK0 := hbadK ℓ hparts.1 (n/ℓ) (k n ℓ) hr.2.2.2.1 (class_parameters_valid n ℓ hr.2.1)
  have hK1 := hbadK ℓ hparts.1 ((n+1)/ℓ) (k (n+1) ℓ) hr.2.2.2.2 (class_parameters_valid (n+1) ℓ hr.2.2.1)
  have hX := rational_argument_Vge ℓ p q hq hno
  by_contra hFail
  push_neg at hFail
  obtain ⟨hzero,hzero1⟩ := hFail
  have hTie : tied n ℓ := by
    by_contra h
    exact (pointwise_nv z n ℓ hzu h1u hr.2.1 hK0 (fun he=>False.elim (h he)) ((p:ℚ)/q) hX).2.2 hzero
  have hTie1 : tied (n+1) ℓ := by
    by_contra h
    exact (pointwise_nv z (n+1) ℓ hzu h1u hr.2.2.1 hK1 (fun he=>False.elim (h he)) ((p:ℚ)/q) hX).2.2 hzero1
  have hnotU : ¬Unit ℓ (Tprime z n ℓ:Padic ℓ) := by
    intro he
    exact (pointwise_nv z n ℓ hzu h1u hr.2.1 hK0 (fun _=>he) ((p:ℚ)/q) hX).2.2 hzero
  have hnotU1 : ¬Unit ℓ (Tprime z (n+1) ℓ:Padic ℓ) := by
    intro he
    exact (pointwise_nv z (n+1) ℓ hzu h1u hr.2.2.1 hK1 (fun _=>he) ((p:ℚ)/q) hX).2.2 hzero1
  have hc2 := (c1_c2_unit z (n/ℓ) (k n ℓ) ℓ (class_parameters_valid n ℓ hr.2.1)
    (tied_k_pos n ℓ hTie) hK0).2
  have hv0 := Tprime_Vge_of_not_unit z n ℓ hzu h1u hr.2.1 hnotU
  have hv1 := Tprime_Vge_of_not_unit z (n+1) ℓ hzu h1u hr.2.2.1 hnotU1
  have hp := pair_obstruction z n ℓ hr.1 hr.2.1 hr.2.2.1 hzu h1u hTie hTie1 hc2 hv0 hv1
  have hp' : (pairPoly (reduceInt ℓ (zInteger z ℓ hzu))⁻¹).eval (n:ZMod ℓ)=0 := by
    simpa only [ZMod.natCast_self,EuclideanDomain.mod_zero] using hp
  exact hresnot (hResid ℓ hparts.2.1 hzu n hp')
#print axioms bandNV_li2
end
end CatalanCore.Li2.NV
