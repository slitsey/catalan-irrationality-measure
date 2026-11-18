module
public import CatalanCore.Li2.NV.LocalExpansion
public import CatalanCore.Arith.Hybrid.LemmaE.Gauss
public import CatalanCore.Arith.Hybrid.RankGLE
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
private theorem rational_unit_of_norm (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ)
    (hq : Unit ℓ (q:Padic ℓ)) : q≠0 ∧ padicValRat ℓ q=0 := by
  have hn : (q:Padic ℓ)≠0:=by
    intro h
    have hh:=hq
    simp only [Unit,h,norm_zero] at hh
    exact zero_ne_one hh
  refine ⟨by exact_mod_cast hn,?_⟩
  have hp : (1:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hv:=Padic.norm_eq_zpow_neg_valuation hn
  rw [Padic.valuation_ratCast,hq] at hv
  have he : -(padicValRat ℓ q)=0:=(zpow_right_strictMono₀ hp).injective
    (hv.symm.trans (zpow_zero (ℓ:ℝ)).symm)
  exact neg_eq_zero.mp he
private theorem denominator_derivative (S : Finset ℕ) (m : ℕ) (hm : m∈S) :
    (poleProd S).derivative.eval (-(m:ℚ))=∏ n∈S.erase m,((n:ℚ)-m) := by
  classical
  have hp : poleProd S=(X+C (m:ℚ))*poleProd (S.erase m) :=
    (Finset.mul_prod_erase S (fun m : ℕ=>X+C (m:ℚ)) hm).symm
  rw [hp]
  simp [poleProd,derivative_mul,eval_prod,sub_eq_add_neg,add_comm]
private theorem integer_poleCoeff_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀ m∈S,m<ℓ) (m : ℕ) (hm : m∈S) :
    Intg ℓ (poleCoeff (P.map (Int.castRingHom ℚ)) S m:Padic ℓ) := by
  classical
  have hn : ‖(((P.map (Int.castRingHom ℚ)).eval (-(m:ℚ)):ℚ):Padic ℓ)‖≤1:=by
    rw [show -(m:ℚ)=((-(m:ℤ):ℤ):ℚ) by simp,Polynomial.eval_intCast_map]
    simpa using!
      PadicInt.norm_le_one ((P.eval (-(m:ℤ)):ℤ):PadicInt ℓ)
  have hd : ‖((∏ n∈S.erase m,((n:ℚ)-m):ℚ):Padic ℓ)‖=1 := by
    push_cast
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro n hn
    have hni:=Finset.mem_erase.mp hn
    have hnon : ¬(ℓ:ℤ)∣(n:ℤ)-m:=by
      intro he
      have hEq : (n:ℤ)%(ℓ:ℤ)=(m:ℤ)%(ℓ:ℤ):=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd he)
      rw [←Int.natCast_mod,←Int.natCast_mod,
        Nat.mod_eq_of_lt (hS n hni.2),Nat.mod_eq_of_lt (hS m hm),Int.natCast_inj] at hEq
      exact hni.1 hEq
    have hu : ‖(((n:ℤ)-m:ℤ):PadicInt ℓ)‖=1:=le_antisymm (PadicInt.norm_le_one _)
      (le_of_not_gt (by rwa [PadicInt.norm_int_lt_one_iff_dvd]))
    simpa using! hu
  unfold Intg poleCoeff
  rw [denominator_derivative S m hm,Rat.cast_div,norm_div,hd,div_one]
  exact hn
private theorem integer_quotient_coeff_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (i : ℕ) :
    Intg ℓ (((P.map (Int.castRingHom ℚ) /ₘ poleProd S).coeff i):Padic ℓ) := by
  classical
  let D : ℤ[X]:=∏ m∈S,(X+C (m:ℤ))
  have hD : D.Monic:=Polynomial.monic_prod_of_monic _ _ (fun m hm=>monic_X_add_C _)
  have hmap : D.map (Int.castRingHom ℚ)=poleProd S:=by
    simp only [D,poleProd,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_X,
      Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast]
  rw [←hmap,←Polynomial.map_divByMonic _ hD,Polynomial.coeff_map]
  simpa only [Int.coe_castRingHom,Int.cast_natCast,Rat.cast_intCast,
    Intg,PadicInt.norm_def,PadicInt.coe_intCast] using PadicInt.norm_le_one ((P /ₘ D).coeff i:PadicInt ℓ)

private theorem intg_rat_VG (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ)
    (hq : Intg ℓ (q:Padic ℓ)) : Port.Li2.VG ℓ q 0 := by
  apply (Port.Li2.VG_iff_padic_norm_le q 0).mpr
  simpa only [Intg,Rat.cast_zero,neg_zero,Real.rpow_zero] using hq
private theorem omega_factor (z : ℚ) (hz : z≠0) (m : ℕ) :
    omega z m=z^(-(m:ℤ))*tauK z m := by
  unfold omega tauK
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show (b:ℤ)-m=-(m:ℤ)+(b:ℤ) by omega,zpow_add₀ hz]
  simp only [zpow_natCast]
  ring


private def weightNumInt (A : TypeKey) : ℤ[X]:=
  match A.kind with
  | .V=>∏ j∈Finset.range A.a,(X+C (j:ℤ))^2
  | .U=>X*∏ j∈Finset.Icc 1 A.a,(X+C (j:ℤ))^2
private theorem weightNumInt_map (A : TypeKey) :
    (weightNumInt A).map (Int.castRingHom ℚ)=weightNum A := by
  cases hk : A.kind <;>
    simp only [weightNumInt,weightNum,hk,Polynomial.map_prod,Polynomial.map_pow,
      Polynomial.map_mul,Polynomial.map_add,Polynomial.map_X,Polynomial.map_C,
      Int.coe_castRingHom,Int.cast_natCast]
private theorem weight_fraction (A : TypeKey) (e : ℕ) :
    rfX^e*weight A=rfPoly (((X:ℤ[X])^e*weightNumInt A).map (Int.castRingHom ℚ))/
      rfPoly (poleProd (poleSet A)) := by
  rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,weightNumInt_map]
  simp only [rfX,weight,weightDen,poleProd,rfPoly,map_mul,map_pow]
  ring

private theorem regularV_integer_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀m∈S,m<ℓ) :
    Intg ℓ ((regularV z (rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)):ℚ):Padic ℓ) := by
  have hu:=rational_unit_of_norm ℓ z hz
  have hv:=rational_unit_of_norm ℓ (1-z) h1
  have hz0 : Port.Li2.VG ℓ z 0:=Or.inr (by rw [hu.2];norm_num)
  have hi:=Port.Li2.rational_unit_inverse_VG z hu.1 hu.2
  have hreg : Port.Li2.VG ℓ (z/(1-z)) 0:=by
    simpa only [div_eq_mul_inv,zero_add] using hz0.mul (Port.Li2.rational_unit_inverse_VG (1-z) hv.1 hv.2)
  have hw : z≠1:=by intro he;apply hv.1;simp [he]
  apply Port.Li2.padic_norm_le_one_of_VG
  rw [regularV_fraction _ _ _ hu.1]
  apply Port.Li2.VG.add
  · apply Port.Li2.VG.sum
    intro m hm
    have hc:=intg_rat_VG ℓ _ (integer_poleCoeff_integral ℓ P S hS m hm)
    have hom : Port.Li2.VG ℓ (omega z m) 0:=by
      rw [omega_factor z hu.1,_root_.zpow_neg,zpow_natCast]
      simpa only [Port.Li2.parameterTau,tauK,zero_mul,mul_zero,zero_add,inv_pow] using
        (hi.pow m).mul (Port.Li2.parameterTau_VG z hz0 m (hS m hm))
    simpa only [zero_add] using hc.mul hom
  · apply Port.Li2.VG.sum
    intro j hj
    have hc:=intg_rat_VG ℓ _ (integer_quotient_coeff_integral ℓ P S j)
    rw [liNeg_eq_parameterMoment z hw]
    simpa only [zero_add] using ((Port.Li2.VG.natCast (p:=ℓ) j).mul hc).mul
      (Port.Li2.parameterMoment_VG ℓ z hreg (j-1))
theorem L_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (A : TypeKey) (hc : A.c<ℓ) (e : ℕ) : Intg ℓ (L A z (X^e):Padic ℓ) := by
  have hS : ∀m∈poleSet A,m<ℓ:=by
    intro m hm
    cases hk : A.kind <;> simp only [poleSet,hk,Finset.mem_Ico,Finset.mem_Ioc] at hm <;> omega
  have hh:=regularV_integer_integral z ℓ hz h1 ((X:ℤ[X])^e*weightNumInt A) (poleSet A) hS
  rw [←weight_fraction] at hh
  simpa only [L,rfPoly,rfX,map_pow] using hh
private theorem unit_of_valuation (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ)
    (hq : q≠0) (hv : padicValRat ℓ q=0) : Unit ℓ (q:Padic ℓ) := by
  unfold Unit
  rw [Padic.eq_padicNorm,padicNorm.eq_zpow_of_nonzero hq,hv]
  norm_num
private theorem nonmatching_unit (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (j : ℕ)
    (hj : j%ℓ≠s.val) : Unit ℓ (((j:ℚ)-s:ℚ):Padic ℓ) := by
  have hu:=Port.Li2.nonmatching_rational_unit (p:=ℓ) s.val j s.isLt hj
  exact unit_of_valuation ℓ _ hu.1 hu.2
private theorem kappa_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) : Unit ℓ (kappa n ℓ s) := by
  unfold Unit kappa kappaQ
  push_cast
  rw [norm_div,norm_prod,norm_prod]
  have hn : (∏ i∈(Finset.Icc 1 n).filter (fun i=>i%ℓ≠s.val),‖((i:Padic ℓ)-s)^3‖)=1:=by
    apply Finset.prod_eq_one
    intro i hi
    rw [norm_pow]
    have hu:=nonmatching_unit ℓ s i (Finset.mem_filter.mp hi).2
    have hu' : ‖(i:Padic ℓ)-s‖=1:=by simpa only [Unit,Rat.cast_sub,Rat.cast_natCast] using hu
    rw [hu']
    norm_num
  have hd : (∏ j∈(Finset.Icc 1 (4*n)).filter (fun j=>j%ℓ≠s.val),‖(j:Padic ℓ)-s‖)=1:=by
    apply Finset.prod_eq_one
    intro j hj
    simpa only [Unit,Rat.cast_sub,Rat.cast_natCast] using nonmatching_unit ℓ s j (Finset.mem_filter.mp hj).2
  rw [hn,hd]
  norm_num
private def crtTailInt (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ) : ℤ[X]:=
  if s=P.1 then crtPiInt n ℓ s else
    (X+C (P.1.val:ℤ))^P.2.val*
      ∏ t∈(Finset.univ.erase P.1).erase s,(X+C (t.val:ℤ))^(m n ℓ t)
private theorem crtEInt_factor (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ) :
    crtEInt n ℓ P=(X+C (s.val:ℤ))^(d n ℓ s P)*crtTailInt n ℓ s P := by
  classical
  by_cases hs : s=P.1
  · subst s
    simp only [crtEInt,crtTailInt,d,if_pos rfl,ite_true]
  · have hm : s∈Finset.univ.erase P.1:=by simp [hs]
    have hp : (∏ t∈Finset.univ.erase P.1,(X+C (t.val:ℤ))^(m n ℓ t))=
        (X+C (s.val:ℤ))^(m n ℓ s)*
          ∏ t∈(Finset.univ.erase P.1).erase s,(X+C (t.val:ℤ))^(m n ℓ t):=
      (Finset.mul_prod_erase (Finset.univ.erase P.1)
        (fun t : Fin ℓ=>(X+C (t.val:ℤ))^(m n ℓ t)) hm).symm
    rw [crtEInt,crtPiInt,hp]
    simp only [crtTailInt,d,if_neg hs]
    ring
private theorem crt_pair_quotient (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) :
    crtE n ℓ P*crtE n ℓ Q /ₘ (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)=
      (crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ) := by
  have hp:=congrArg (Polynomial.map (Int.castRingHom ℚ)) (crtEInt_factor n ℓ s P)
  have hq:=congrArg (Polynomial.map (Int.castRingHom ℚ)) (crtEInt_factor n ℓ s Q)
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast] at hp hq
  rw [crtE,crtE,hp,hq]
  have he : (X+C (s:ℚ))^(d n ℓ s P)*(crtTailInt n ℓ s P).map (Int.castRingHom ℚ)*
      ((X+C (s:ℚ))^(d n ℓ s Q)*(crtTailInt n ℓ s Q).map (Int.castRingHom ℚ))=
      (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)*
        ((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ)) := by
    rw [pow_add,Polynomial.map_mul]
    ring
  rw [he]
  exact Polynomial.mul_divByMonic_cancel_left _ ((monic_X_add_C _).pow _)

private theorem crt_linear_unit (ℓ : ℕ) [Fact ℓ.Prime] (s t : Fin ℓ) (ht : t≠s) :
    Unit ℓ ((((X+C (t.val:ℤ):ℤ[X]).eval (-(s.val:ℤ))):ℤ):Padic ℓ) := by
  have hu:=nonmatching_unit ℓ s t.val (by
    rw [Nat.mod_eq_of_lt t.isLt]
    exact fun h=>ht (Fin.ext h))
  simpa only [Unit,eval_add,eval_X,eval_C,Int.cast_add,Int.cast_neg,Int.cast_natCast,
    Rat.cast_sub,Rat.cast_natCast,sub_eq_add_neg,add_comm] using! hu
private theorem crt_product_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ)
    (S : Finset (Fin ℓ)) (hS : ∀t∈S,t≠s) :
    Unit ℓ ((((∏ t∈S,(X+C (t.val:ℤ))^(m n ℓ t):ℤ[X]).eval (-(s.val:ℤ))):ℤ):Padic ℓ) := by
  unfold Unit
  simp only [eval_prod,eval_pow,Int.cast_prod,Int.cast_pow,norm_prod,norm_pow]
  apply Finset.prod_eq_one
  intro t ht
  have hu:=crt_linear_unit ℓ s t (hS t ht)
  change ‖(((X+C (t.val:ℤ):ℤ[X]).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hu
  rw [hu]
  simp
private theorem crtTailInt_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : Ix n ℓ) :
    Unit ℓ (((crtTailInt n ℓ s P).eval (-(s.val:ℤ)):ℤ):Padic ℓ) := by
  classical
  unfold crtTailInt
  split_ifs with hs
  · unfold crtPiInt
    exact crt_product_unit n ℓ s _ (fun t ht=> (Finset.mem_erase.mp ht).1)
  · unfold Unit
    rw [eval_mul,eval_pow,Int.cast_mul,Int.cast_pow,norm_mul,norm_pow]
    have hu:=crt_linear_unit ℓ s P.1 (Ne.symm hs)
    have hv:=crt_product_unit n ℓ s ((Finset.univ.erase P.1).erase s)
      (fun t ht=>(Finset.mem_erase.mp ht).1)
    change ‖(((X+C (P.1.val:ℤ):ℤ[X]).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hu
    rw [hu]
    simpa only [Unit,one_pow,one_mul] using hv
private theorem crt_pair_constant_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P Q : Ix n ℓ) :
    Unit ℓ (((crtE n ℓ P*crtE n ℓ Q /ₘ
      (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ)):ℚ):Padic ℓ) := by
  rw [crt_pair_quotient]
  have he : -(s:ℚ)=((-(s.val:ℤ):ℤ):ℚ):=by simp
  rw [he,Polynomial.eval_intCast_map]
  simp only [Int.coe_castRingHom,Rat.cast_intCast,eval_mul,Int.cast_mul]
  unfold Unit
  push_cast
  rw [norm_mul]
  have hp:=crtTailInt_unit n ℓ s P
  have hq:=crtTailInt_unit n ℓ s Q
  change ‖(((crtTailInt n ℓ s P).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hp
  change ‖(((crtTailInt n ℓ s Q).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hq
  simpa using! congrArg₂ (fun a b : ℝ=>a*b) hp hq


private theorem crtPi_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    Unit ℓ (((crtPi n ℓ s).eval (-(s:ℚ)):ℚ):Padic ℓ) := by
  classical
  unfold crtPi
  rw [show -(s:ℚ)=((-(s.val:ℤ):ℤ):ℚ) by simp,Polynomial.eval_intCast_map]
  exact crt_product_unit n ℓ s (Finset.univ.erase s) (fun t ht=>(Finset.mem_erase.mp ht).1)
theorem uQ_unit (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (s : Fin ℓ) :
    Unit ℓ (uQ z n ℓ s:Padic ℓ) := by
  have hpi:=crtPi_unit n ℓ s
  have hk:=kappa_unit n ℓ s
  by_cases hs : s.val=0
  · have hh : Unit ℓ (kappa n ℓ s*(((crtPi n ℓ s).eval (-(s:ℚ)):ℚ):Padic ℓ)^2):=by
      unfold Unit
      rw [norm_mul,norm_pow,hk,hpi]
      norm_num
    simpa only [uQ,hs,ite_true,one_mul,Rat.cast_mul,Rat.cast_pow,kappa] using hh
  · have hn : ¬ℓ∣s.val:=Nat.not_dvd_of_pos_of_lt (by omega) s.isLt
    have hsu : ‖(s.val:PadicInt ℓ)‖=1:=le_antisymm (PadicInt.norm_le_one _)
      (le_of_not_gt (by rwa [PadicInt.norm_natCast_lt_one_iff]))
    have hs' : ‖(s.val:Padic ℓ)‖=1:=by simpa only [PadicInt.norm_def,PadicInt.coe_natCast] using hsu
    simp only [uQ,if_neg hs,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_zpow,Rat.cast_natCast]
    change ‖(-(s.val:Padic ℓ)*(z:Padic ℓ)^(-(s.val:ℤ)))*kappa n ℓ s*
      (((crtPi n ℓ s).eval (-(s:ℚ)):ℚ):Padic ℓ)^2‖=1
    rw [norm_mul,norm_mul,norm_mul,norm_neg,norm_zpow,norm_pow,hz,hs',hk,hpi]
    norm_num
noncomputable def reduceInt (ℓ : ℕ) [Fact ℓ.Prime] : PadicInt ℓ →+* ZMod ℓ :=
  PadicInt.toZMod
noncomputable def zInteger (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) : PadicInt ℓ := ⟨(z:Padic ℓ),hz.le⟩
structure ReductionData (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime] where
  units : Fin ℓ→PadicInt ℓ
  units_cast : ∀ s, (units s:Padic ℓ)=(uQ z n ℓ s:Padic ℓ)
  moments : TypeKey→ℕ→PadicInt ℓ
  moments_cast : ∀ A, A.a≤A.c → A.c<ℓ → ∀ e,
    (moments A e:Padic ℓ)=(L A z (X^e):Padic ℓ)

noncomputable def redU {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) : ZMod ℓ := reduceInt ℓ (R.units s)
noncomputable def redMoment {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) (e : ℕ) : ZMod ℓ :=
  reduceInt ℓ (R.moments A e)
noncomputable def redK {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) : ZMod ℓ :=
  (Matrix.of fun i j : Fin A.size => redMoment R A (i.val+j.val)).det
noncomputable def S0red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) : ZMod ℓ :=
  ∑ s : Fin ℓ, if s.val∈Cset n ℓ then redU R s/(s.val:ZMod ℓ)^2 else 0
noncomputable def expectedDiagonal {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (P Q : Ix n ℓ) : ZMod ℓ :=
  if P.1=Q.1 then
    redU R P.1*redMoment R (classKey n ℓ P.1) (P.2.val+Q.2.val) +
      if P.1.val=0 ∧ P.2.val+1=m0 n ℓ ∧ Q.2.val+1=m0 n ℓ then
        S0red R*redMoment R (keyC n ℓ) (2*mC n ℓ) else 0
  else if P.1.val∈Cset n ℓ ∧ Q.1.val=0 ∧ Q.2.val+1=m0 n ℓ then
    redU R P.1/(-(P.1.val:ZMod ℓ))*redMoment R (keyC n ℓ) (P.2.val+mC n ℓ)
  else if Q.1.val∈Cset n ℓ ∧ P.1.val=0 ∧ P.2.val+1=m0 n ℓ then
    redU R Q.1/(-(Q.1.val:ZMod ℓ))*redMoment R (keyC n ℓ) (Q.2.val+mC n ℓ)
  else 0
noncomputable def expectedReduction {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (upper : Matrix (Ix n ℓ) (Ix n ℓ) (ZMod ℓ)) :
    Matrix (Ix n ℓ) (Ix n ℓ) (ZMod ℓ) :=
  fun P Q => if nu n ℓ P.1%2=nu n ℓ Q.1%2 then expectedDiagonal R P Q
    else if nu n ℓ P.1%2=0 then upper P Q else 0
abbrev EvenIx (n ℓ : ℕ) := {P : Ix n ℓ // nu n ℓ P.1%2=0}
abbrev OddIx (n ℓ : ℕ) := {P : Ix n ℓ // nu n ℓ P.1%2≠0}
abbrev TiedIx (n ℓ : ℕ) :=
  {P : Ix n ℓ // P.1.val=0 ∨ classType n ℓ P.1=.C}
noncomputable def tiedBlock {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) : Matrix (TiedIx n ℓ) (TiedIx n ℓ) (ZMod ℓ) :=
  fun P Q => expectedDiagonal R P.val Q.val
theorem reduction_data_exists (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) :
    Nonempty (ReductionData z n ℓ) := by
  classical
  refine ⟨{ units:=fun s=>⟨(uQ z n ℓ s:Padic ℓ),(uQ_unit z n ℓ hz s).le⟩
            units_cast:=fun s=>rfl
            moments:=fun A e=>if hc : A.c<ℓ then ⟨(L A z (X^e):Padic ℓ),L_integral z ℓ hz h1 A hc e⟩ else 0
            moments_cast:=?_
          }⟩
  intro A hac hc e
  simp only [dif_pos hc]
theorem rat_integral_iff_locRing (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ) :
    Intg ℓ (q:Padic ℓ) ↔ q∈Basic.LocRing ℓ := by
  rw [Arith.Hybrid.mem_locRing_iff_padicNorm]
  unfold Intg
  rw [Padic.eq_padicNorm]
  exact_mod_cast Iff.rfl
def locToPadicInt (ℓ : ℕ) [Fact ℓ.Prime] : Basic.LocRing ℓ→+*PadicInt ℓ where
  toFun q:=⟨((q:ℚ):Padic ℓ),(rat_integral_iff_locRing ℓ q).mpr q.property⟩
  map_zero':=by apply PadicInt.ext;simp
  map_one':=by apply PadicInt.ext;simp
  map_add' a b:=by apply PadicInt.ext;simp
  map_mul' a b:=by apply PadicInt.ext;simp
theorem locToPadicInt_red (ℓ : ℕ) [Fact ℓ.Prime] (q : Basic.LocRing ℓ) :
    PadicInt.toZMod (locToPadicInt ℓ q)=Arith.Hybrid.redQ ℓ q := by
  have hqd : q*((q:ℚ).den:Basic.LocRing ℓ)=((q:ℚ).num:Basic.LocRing ℓ):=by
    apply Subtype.ext
    exact ((div_eq_iff (by exact_mod_cast (q:ℚ).den_ne_zero)).mp (Rat.num_div_den (q:ℚ))).symm
  let φ : Basic.LocRing ℓ→+*ZMod ℓ:=PadicInt.toZMod.comp (locToPadicInt ℓ)
  have hφ:=congrArg φ hqd
  have hψ:=congrArg (Arith.Hybrid.redQ ℓ) hqd
  simp only [map_mul,map_natCast,map_intCast] at hφ hψ
  have hd : ((q:ℚ).den:ZMod ℓ)≠0:=Arith.Hybrid.den_cast_ne_zero ℓ q.property
  exact mul_right_cancel₀ hd (hφ.trans hψ.symm)
theorem reduce_eq_of_Vge (ℓ : ℕ) [Fact ℓ.Prime] (x y : PadicInt ℓ)
    (h : Vge ℓ ((x:Padic ℓ)-(y:Padic ℓ)) 1) : PadicInt.toZMod x=PadicInt.toZMod y := by
  have hp : (1:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hnorm : ‖x-y‖<1:=by
    have hh : ‖(x:Padic ℓ)-(y:Padic ℓ)‖≤(ℓ:ℝ)⁻¹:=by
      simpa only [Vge,Int.cast_one,Real.rpow_neg_one] using h
    simpa only [PadicInt.norm_def,PadicInt.coe_sub] using hh.trans_lt (inv_lt_one_of_one_lt₀ hp)
  have hk : x-y∈RingHom.ker (PadicInt.toZMod : PadicInt ℓ→+*ZMod ℓ):=by
    rw [PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton]
    exact (PadicInt.norm_lt_one_iff_dvd _).mp hnorm
  rw [RingHom.mem_ker,map_sub,sub_eq_zero] at hk
  exact hk

theorem reduce_ne_zero_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ)
    (hx : Unit ℓ (x:Padic ℓ)) : reduceInt ℓ x≠0 := by
  intro he
  have hk : x∈RingHom.ker (PadicInt.toZMod:PadicInt ℓ→+*ZMod ℓ):=he
  rw [PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton] at hk
  have hn:=(PadicInt.norm_lt_one_iff_dvd x).mpr hk
  have hx' : ‖x‖=1:=hx
  rw [hx'] at hn
  exact lt_irrefl 1 hn
theorem redU_ne_zero (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (R : ReductionData z n ℓ) (s : Fin ℓ) : redU R s≠0 := by
  apply reduce_ne_zero_of_unit ℓ (R.units s)
  rw [R.units_cast]
  exact uQ_unit z n ℓ hz s
theorem redK_ne_zero (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (A : TypeKey) (hac : A.a≤A.c) (hc : A.c<ℓ)
    (hK : Unit ℓ (K A z:Padic ℓ)) : redK R A≠0 := by
  classical
  let M : Matrix (Fin A.size) (Fin A.size) (PadicInt ℓ):=fun i j=>R.moments A (i.val+j.val)
  let N : Matrix (Fin A.size) (Fin A.size) ℚ:=fun i j=>L A z (X^(i.val+j.val))
  have hm : PadicInt.Coe.ringHom.mapMatrix M=(Rat.castHom (Padic ℓ)).mapMatrix N:=by
    ext i j
    exact R.moments_cast A hac hc (i.val+j.val)
  have hd:=congrArg Matrix.det hm
  rw [←RingHom.map_det,←RingHom.map_det] at hd
  simp only [PadicInt.Coe.ringHom_apply] at hd
  have hunit : Unit ℓ ((M.det:PadicInt ℓ):Padic ℓ):=by
    rw [hd]
    exact hK
  have hn:=reduce_ne_zero_of_unit ℓ M.det hunit
  have he : redK R A=reduceInt ℓ M.det:=by
    rw [(reduceInt ℓ).map_det]
    rfl
  rw [he]
  exact hn
#print axioms L_integral
#print axioms uQ_unit
#print axioms rat_integral_iff_locRing
#print axioms locToPadicInt_red
#print axioms reduce_eq_of_Vge
#print axioms reduce_ne_zero_of_unit
#print axioms reduction_data_exists
#print axioms redU_ne_zero
#print axioms redK_ne_zero
end
end CatalanCore.Li2.NV
