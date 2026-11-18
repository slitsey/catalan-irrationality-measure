module
public import CatalanCore.Li2.NVMod.LaurentBounds
public import CatalanCore.Li2.NVMod.InfinityMap
public import CatalanCore.Li2.NVMod.RationalRules
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.Polynomial.Pochhammer
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem powerSeries_nonneg (f : PowerSeries ℚ) :
    Oge (HahnSeries.ofPowerSeries ℤ ℚ f) 0 := by
  intro e he
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨n,hn⟩
  change (n:ℤ)=e at hn
  omega
private theorem geometric_inverse (d : ℕ) :
    ((1-hX : HahnSeries ℤ ℚ)^(d+1))⁻¹=
      HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk (fun n=>(Nat.choose (d+n) d:ℚ))) := by
  have hh:=congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
    (PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℚ d)
  symm
  apply eq_inv_of_mul_eq_one_left
  simpa only [map_mul,map_pow,map_sub,map_one,HahnSeries.ofPowerSeries_X,hX] using hh
private theorem geometric_inverse_nonneg (d : ℕ) :
    Oge (((1-hX : HahnSeries ℤ ℚ)^(d+1))⁻¹) 0 := by
  rw [geometric_inverse]
  exact powerSeries_nonneg _
private theorem geometric_inverse_coeff (d t : ℕ) :
    (((1-hX : HahnSeries ℤ ℚ)^(d+1))⁻¹).coeff (t:ℤ)=(Nat.choose (d+t) d:ℚ) := by
  rw [geometric_inverse,HahnSeries.ofPowerSeries_apply_coeff,PowerSeries.coeff_mk]
theorem shifted_geometric (d : ℕ) :
    Oge ((hX : HahnSeries ℤ ℚ)/((1-hX)^(d+1))) 1 ∧
    ∀ t : ℕ,((hX : HahnSeries ℤ ℚ)/((1-hX)^(d+1))).coeff (t:ℤ)=
      if t=0 then 0 else (Nat.choose (d+t-1) d:ℚ) := by
  constructor
  · simpa only [hX,div_eq_mul_inv,add_zero] using (Oge.single 1 (1:ℚ)).mul (geometric_inverse_nonneg d)
  · intro t
    rw [div_eq_mul_inv]
    change (HahnSeries.single 1 (1:ℚ)*((1-hX : HahnSeries ℤ ℚ)^(d+1))⁻¹).coeff (t:ℤ)=_
    rw [HahnSeries.coeff_single_mul,one_mul]
    by_cases ht : t=0
    · subst t
      rw [if_pos rfl]
      exact geometric_inverse_nonneg d _ (by omega)
    · rw [if_neg ht]
      have he : (t:ℤ)-1=((t-1:ℕ):ℤ) := by omega
      rw [he,geometric_inverse_coeff]
      congr 2
      omega

private theorem stirling_polynomial (j : ℕ) : (X:ℚ[X])^j=
    ∑ i∈Finset.range (j+1),C (Nat.stirlingSecond j i:ℚ)*descPochhammer ℚ i := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun n:ℕ=>(n:ℚ)))).mono
  rintro x ⟨n,rfl⟩
  change ((X:ℚ[X])^j).eval (n:ℚ)=_
  simp only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,descPochhammer_eval_eq_descFactorial]
  exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n j
private theorem descending_negative (t i : ℕ) :
    (descPochhammer ℚ i).eval (-(t:ℚ))=(-1:ℚ)^i*(t.ascFactorial i:ℚ) := by
  have hh:=ascPochhammer_eval_neg_eq_descPochhammer (R:=ℚ) (-(t:ℚ)) i
  rw [neg_neg,ascPochhammer_nat_eq_natCast_ascFactorial] at hh
  have hs : (-1:ℚ)^i*(-1)^i=1 := by rw [←mul_pow];norm_num
  calc
    _=((-1:ℚ)^i*(-1)^i)*(descPochhammer ℚ i).eval (-(t:ℚ)) := by rw [hs,one_mul]
    _=(-1:ℚ)^i*(t.ascFactorial i:ℚ) := by rw [mul_assoc,←hh]
theorem stirling_rising_reflection (j t : ℕ) :
    (∑ i∈Finset.range (j+1),(Nat.stirlingSecond j i:ℚ)*(-1:ℚ)^(i+1)*(t.ascFactorial i:ℚ))=
      (-1:ℚ)^(j+1)*(t:ℚ)^j := by
  have hh:=congrArg (Polynomial.eval (-(t:ℚ))) (stirling_polynomial j)
  simp only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C] at hh
  simp_rw [descending_negative] at hh
  have he : (-(t:ℚ))^j=(-1:ℚ)^j*(t:ℚ)^j := by rw [neg_eq_neg_one_mul,mul_pow]
  rw [he] at hh
  calc
    _=-(∑ i∈Finset.range (j+1),(Nat.stirlingSecond j i:ℚ)*((-1:ℚ)^i*(t.ascFactorial i:ℚ))) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    _=-((-1:ℚ)^j*(t:ℚ)^j) := by rw [←hh]
    _=_ := by rw [pow_succ];ring

private theorem coeff_sum_hahn {ι : Type*} (S : Finset ι)
    (f : ι→HahnSeries ℤ ℚ) (e : ℤ) :
    (∑ i∈S,f i).coeff e=∑ i∈S,(f i).coeff e := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,HahnSeries.coeff_add,ih]

private theorem inverse_variable_term {F : Type*} [Field F] (x : F) (hx : x≠0) (i : ℕ) :
    (x⁻¹)^i/(1-x⁻¹)^(i+1)=(-1:F)^(i+1)*x/(1-x)^(i+1) := by
  have hd : 1-x⁻¹=(x-1)/x := by field_simp [hx] <;> ring
  have hn : (x⁻¹)^i*x^(i+1)=x := by
    rw [pow_succ,_root_.inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero i hx),one_mul]
  rw [hd,div_pow,div_div_eq_mul_div,hn,show x-1=-(1-x) by ring,neg_pow]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_pow,inv_neg,inv_one]
  ring_nf <;> simp only [inv_neg_one]
private theorem inverse_variable_zero {F : Type*} [Field F] (x : F) (hx : x≠0) :
    liNeg 0 x⁻¹=-(1-x)⁻¹ := by
  rw [liNeg,if_pos rfl]
  have hd : 1-x⁻¹=(x-1)/x := by field_simp [hx] <;> ring
  rw [hd,div_div_eq_mul_div,inv_mul_cancel₀ hx,one_div,show x-1=-(1-x) by ring,inv_neg]
private theorem positive_liNeg_inverse (j : ℕ) (hj : j≠0) :
    liNeg j ((hX : HahnSeries ℤ ℚ)⁻¹)=
      ∑ i∈Finset.Icc 1 j,HahnSeries.C ((Nat.stirlingSecond j i:ℚ)*(Nat.factorial i:ℚ)*(-1:ℚ)^(i+1))*
        ((hX : HahnSeries ℤ ℚ)/(1-hX)^(i+1)) := by
  rw [liNeg,if_neg hj]
  apply Finset.sum_congr rfl
  intro i hi
  have hx : (hX : HahnSeries ℤ ℚ)≠0 := HahnSeries.single_ne_zero one_ne_zero
  calc
    _=(Nat.stirlingSecond j i:HahnSeries ℤ ℚ)*(Nat.factorial i:HahnSeries ℤ ℚ)*
        ((hX⁻¹)^i/(1-hX⁻¹)^(i+1)) := by ring
    _=(Nat.stirlingSecond j i:HahnSeries ℤ ℚ)*(Nat.factorial i:HahnSeries ℤ ℚ)*
        ((-1:HahnSeries ℤ ℚ)^(i+1)*hX/(1-hX)^(i+1)) := by rw [inverse_variable_term hX hx i]
    _=_ := by
      simp only [map_mul,map_pow,map_natCast,map_neg,map_one]
      ring
theorem liNeg_at_infinity (j : ℕ) :
    Oge (liNeg j ((hX : HahnSeries ℤ ℚ)⁻¹)) 0 ∧
      ∀ t : ℕ,(liNeg j ((hX : HahnSeries ℤ ℚ)⁻¹)).coeff (t:ℤ)=-(-(t:ℚ))^j := by
  by_cases hj : j=0
  · subst j
    rw [inverse_variable_zero hX (HahnSeries.single_ne_zero one_ne_zero)]
    have he : (1-hX : HahnSeries ℤ ℚ)⁻¹=((1-hX)^(0+1))⁻¹ := by simp
    rw [he]
    constructor
    · exact (geometric_inverse_nonneg 0).neg
    · intro t
      rw [HahnSeries.coeff_neg,geometric_inverse_coeff]
      norm_num
  · rw [positive_liNeg_inverse j hj]
    constructor
    · apply (Oge.sum _ _ 1 ?_).mono (by omega)
      intro i hi
      simpa only [zero_add] using (Oge.C _).mul (shifted_geometric i).1
    · intro t
      by_cases ht : t=0
      · subst t
        rw [coeff_sum_hahn]
        have he : (∑ i∈Finset.Icc 1 j,
            (HahnSeries.C ((Nat.stirlingSecond j i:ℚ)*(Nat.factorial i:ℚ)*(-1:ℚ)^(i+1))*
              (hX/(1-hX)^(i+1))).coeff (0:ℤ))=0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hg:=(shifted_geometric i).2 0
          rw [Nat.cast_zero,if_pos rfl] at hg
          rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,hg,mul_zero]
        simpa only [Nat.cast_zero,neg_zero,zero_pow hj] using he
      · have hS0 : Nat.stirlingSecond j 0=0 := by
          obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hj
          exact Nat.stirlingSecond_succ_zero a
        have hr:=stirling_rising_reflection j t
        have hset : Finset.range (j+1)=insert 0 (Finset.Icc 1 j) := by
          ext i
          simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
          omega
        rw [hset,Finset.sum_insert (by simp)] at hr
        simp only [hS0,Nat.cast_zero,zero_mul,zero_add] at hr
        calc
          _=∑ i∈Finset.Icc 1 j,(Nat.stirlingSecond j i:ℚ)*(-1:ℚ)^(i+1)*(t.ascFactorial i:ℚ) := by
            rw [coeff_sum_hahn]
            apply Finset.sum_congr rfl
            intro i hi
            rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,(shifted_geometric i).2 t,if_neg ht]
            have ha:=congrArg (fun n:ℕ=>(n:ℚ)) (Nat.ascFactorial_eq_factorial_mul_choose' t i)
            simp only [Nat.cast_mul] at ha
            rw [ha]
            have he : i+t-1=t+i-1 := by omega
            rw [he]
            ring
          _=(-1:ℚ)^(j+1)*(t:ℚ)^j := hr
          _=-(-(t:ℚ))^j := by rw [neg_pow,pow_succ];ring

private theorem inf_hom_X : infRFHahnQ (rfX : RatFunc ℚ)=hX⁻¹ := by
  simp only [infRFHahnQ,rfX,rfPoly,RatFunc.liftRingHom_algebraMap,infPolyHahnQ,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
private theorem inf_hom_C (q : ℚ) : infRFHahnQ (rfPoly (C q))=HahnSeries.C q := by
  simp only [infRFHahnQ,rfPoly,RatFunc.liftRingHom_algebraMap,infPolyHahnQ,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
  rw [eq_ratCast]
  rfl
private theorem inf_omega_expansion (m : ℕ) :
    atInf (omegaRF m)=∑ b∈Icc 1 m,HahnSeries.single ((m:ℤ)-b) ((1:ℚ)/(b:ℚ)^2) := by
  rw [atInf_eq_hom]
  unfold omegaRF
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_div₀,map_zpow₀,inf_hom_X,inf_hom_C]
  rw [inv_zpow,←_root_.zpow_neg,show -((b:ℤ)-m)=((m-b:ℕ):ℤ) by have hh:=(Finset.mem_Icc.mp hb).2;omega,zpow_natCast]
  simp only [hX,HahnSeries.single_pow,nsmul_eq_mul,mul_one,one_pow,
    HahnSeries.C_apply,HahnSeries.single_div_single,sub_zero]
  have hh:=(Finset.mem_Icc.mp hb).2
  rw [Nat.cast_sub hh]
private theorem coeff_sum_inf {ι : Type*} (S : Finset ι) (f : ι→HahnSeries ℤ ℚ) (e : ℤ) :
    (∑ i∈S,f i).coeff e=∑ i∈S,(f i).coeff e := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,HahnSeries.coeff_add,ih]
theorem omega_at_infinity (m : ℕ) : Oge (atInf (omegaRF m)) 0 ∧
    ∀ t : ℕ,(atInf (omegaRF m)).coeff (t:ℤ)=
      if t<m then (1:ℚ)/((m:ℚ)-t)^2 else 0 := by
  classical
  rw [inf_omega_expansion]
  constructor
  · apply Oge.sum
    intro b hb
    exact (Oge.single _ _).mono (by have hh:=(Finset.mem_Icc.mp hb).2;omega)
  · intro t
    rw [coeff_sum_inf]
    by_cases ht : t<m
    · rw [if_pos ht,Finset.sum_eq_single (m-t)]
      · have he : (m:ℤ)-((m-t:ℕ):ℤ)=(t:ℤ) := by omega
        rw [he,HahnSeries.coeff_single_same,Nat.cast_sub (by omega : t≤m)]
      · intro b hb hne
        exact HahnSeries.coeff_single_of_ne (by omega)
      · intro hn
        exact False.elim (hn (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro b hb
      exact HahnSeries.coeff_single_of_ne (by have hh:=(Finset.mem_Icc.mp hb).1;omega)

theorem rfDeriv_eq_audited (F : RatFunc ℚ) : rfDeriv F=
    (rfPoly F.num.derivative*rfPoly F.denom-rfPoly F.num*rfPoly F.denom.derivative)/(rfPoly F.denom)^2 := by
  simp only [rfDeriv,rfPoly,map_mul,map_sub]
theorem rfEval_eq_audited (F : RatFunc ℚ) (x : ℚ) : rfEval F x=RatFunc.eval (RingHom.id ℚ) x F := by
  rfl
private theorem inf_hom_rat (q : ℚ) : infRFHahnQ (algebraMap ℚ (RatFunc ℚ) q)=HahnSeries.C q := by
  rw [eq_ratCast,map_ratCast]
  rfl
private theorem moment_inf_expansion (A : TypeKey) (g : ℚ[X]) :
    atInf (momentRF A g)=
      (∑ m∈poleSet A,HahnSeries.C (residue A m*g.eval (-(m:ℚ)))*atInf (omegaRF m))+
        ∑ k∈Finset.Icc 1 (polyPart A g).natDegree,
          (k:HahnSeries ℤ ℚ)*HahnSeries.C ((polyPart A g).coeff k)*liNeg (k-1) hX⁻¹ := by
  simp only [atInf_eq_hom]
  rw [momentRF_partial_fractions,map_add]
  simp only [map_sum,map_mul,inf_hom_rat,map_natCast,liNeg_map,inf_hom_X]
  simp only [eq_ratCast,map_ratCast]
private theorem derivative_finite_sum (P : ℚ[X]) (x : ℚ) :
    P.derivative.eval x=∑ k∈Finset.Icc 1 P.natDegree,(k:ℚ)*P.coeff k*x^(k-1) := by
  classical
  rw [Polynomial.derivative_eval,Polynomial.sum_over_range _ (by intro k;simp)]
  have hset : Finset.range (P.natDegree+1)=insert 0 (Finset.Icc 1 P.natDegree) := by
    ext k
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [hset,Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero,mul_zero,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  ring
private theorem poly_inf_coeff (P : ℚ[X]) (t : ℕ) :
    (∑ k∈Finset.Icc 1 P.natDegree,
      (k:HahnSeries ℤ ℚ)*HahnSeries.C (P.coeff k)*liNeg (k-1) hX⁻¹).coeff (t:ℤ)=
        -P.derivative.eval (-(t:ℚ)) := by
  rw [coeff_sum_hahn,derivative_finite_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (k:HahnSeries ℤ ℚ)*HahnSeries.C (P.coeff k)=HahnSeries.C ((k:ℚ)*P.coeff k) := by
    simp only [map_mul,map_natCast]
  rw [he,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,(liNeg_at_infinity (k-1)).2 t]
  ring
theorem moment_inf_finite_coeff (A : TypeKey) (g : ℚ[X]) :
    Oge (atInf (momentRF A g)) 0 ∧
      ∀ t : ℕ,(atInf (momentRF A g)).coeff (t:ℤ)=
        (∑ m∈(poleSet A).filter (fun m=>t<m),
          residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2)-
        (polyPart A g).derivative.eval (-(t:ℚ)) := by
  rw [moment_inf_expansion]
  constructor
  · apply Oge.add
    · apply Oge.sum
      intro m hm
      simpa only [zero_add] using (Oge.C _).mul (omega_at_infinity m).1
    · apply Oge.sum
      intro k hk
      have he : (k:HahnSeries ℤ ℚ)*HahnSeries.C ((polyPart A g).coeff k)=
          HahnSeries.C ((k:ℚ)*(polyPart A g).coeff k) := by simp only [map_mul,map_natCast]
      rw [he]
      simpa only [zero_add] using (Oge.C _).mul (liNeg_at_infinity (k-1)).1
  · intro t
    rw [HahnSeries.coeff_add,poly_inf_coeff,sub_eq_add_neg]
    congr 1
    rw [coeff_sum_hahn,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,(omega_at_infinity m).2 t]
    by_cases htm : t<m <;> simp only [htm,ite_true,ite_false,mul_zero]
    ring

private def rfPole (c : ℚ) (m : ℕ) : RatFunc ℚ := rfPoly (C c)/rfPoly (X+C (m:ℚ))
private theorem rfPole_regular (c x : ℚ) (m : ℕ) (hx : x+(m:ℚ)≠0) : RFRegular x (rfPole c m) := by
  apply RFRegular.fraction x _ _ (Polynomial.monic_X_add_C _).ne_zero
  simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using hx
private theorem rfPole_deriv (c : ℚ) (m : ℕ) :
    rfDeriv (rfPole c m)=rfPoly (-C c)/rfPoly ((X+C (m:ℚ))^2) := by
  have hh:=rfDeriv_fraction (rfPole c m) (C c) (X+C (m:ℚ)) (Polynomial.monic_X_add_C _).ne_zero rfl
  simp only [Polynomial.derivative_C,Polynomial.derivative_add,Polynomial.derivative_X,
    add_zero,zero_mul,mul_one,zero_sub] at hh
  simpa only [rfPoly,map_pow] using hh
private theorem rfPole_deriv2 (c : ℚ) (m : ℕ) :
    rfDeriv (rfDeriv (rfPole c m))=rfPoly (C (2*c))/rfPoly ((X+C (m:ℚ))^3) := by
  let Q : ℚ[X] := X+C (m:ℚ)
  have hQ : Q≠0 := (Polynomial.monic_X_add_C _).ne_zero
  have hD : Q.derivative=1 := by simp [Q]
  have hD2 : (Q^2).derivative=2*Q := by norm_num [Polynomial.derivative_pow,hD,map_ofNat]
  have hh:=rfDeriv_fraction (rfDeriv (rfPole c m)) (-C c) (Q^2) (pow_ne_zero 2 hQ) (rfPole_deriv c m)
  have hnum : (-C c).derivative*Q^2-(-C c)*(Q^2).derivative=C (2*c)*Q := by
    rw [Polynomial.derivative_neg,Polynomial.derivative_C,hD2]
    simp only [neg_zero,zero_mul,zero_sub,map_mul,map_ofNat]
    ring
  rw [hnum] at hh
  have hn : rfPoly Q≠0 := RatFunc.algebraMap_ne_zero hQ
  simp only [rfPoly] at hn
  rw [hh]
  change rfPoly (C (2*c)*Q)/(rfPoly (Q^2))^2=rfPoly (C (2*c))/rfPoly (Q^3)
  simp only [rfPoly,map_mul,map_pow]
  field_simp [hn]
  <;> ring
private theorem rfPole_eval_deriv (c x : ℚ) (m : ℕ) (hx : x+(m:ℚ)≠0) :
    rfEval (rfDeriv (rfPole c m)) x=-c/(x+(m:ℚ))^2 := by
  have hQ : (X+C (m:ℚ):ℚ[X])≠0 := (Polynomial.monic_X_add_C _).ne_zero
  have he:=rfEval_fraction (rfDeriv (rfPole c m)) (-C c) ((X+C (m:ℚ))^2) x
    (pow_ne_zero 2 hQ) (by simpa only [Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C] using pow_ne_zero 2 hx) (rfPole_deriv c m)
  simpa only [Polynomial.eval_neg,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X] using he
private theorem rfPole_eval_deriv2 (c x : ℚ) (m : ℕ) (hx : x+(m:ℚ)≠0) :
    rfEval (rfDeriv (rfDeriv (rfPole c m))) x=(2*c)/(x+(m:ℚ))^3 := by
  have hQ : (X+C (m:ℚ):ℚ[X])≠0 := (Polynomial.monic_X_add_C _).ne_zero
  have he:=rfEval_fraction (rfDeriv (rfDeriv (rfPole c m))) (C (2*c)) ((X+C (m:ℚ))^3) x
    (pow_ne_zero 3 hQ) (by simpa only [Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C] using pow_ne_zero 3 hx) (rfPole_deriv2 c m)
  simpa only [Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X] using he
private theorem finite_pf_deriv (R : ℚ[X]) (S : Finset ℕ) (c : ℕ→ℚ) (x : ℚ)
    (hx : ∀ m∈S,x+(m:ℚ)≠0) :
    rfEval (rfDeriv (rfPoly R+∑ m∈S,rfPole (c m) m)) x=
      R.derivative.eval x-∑ m∈S,c m/(x+(m:ℚ))^2 := by
  have hr (m : ℕ) (hm : m∈S) : RFRegular x (rfDeriv (rfPole (c m) m)) :=
    (rfPole_regular (c m) x m (hx m hm)).deriv
  rw [rfDeriv_add,rfDeriv_poly,rfDeriv_sum,
    rfEval_add (RFRegular.poly x _) (RFRegular.sum S _ x hr),rfEval_poly,
    rfEval_sum S _ x hr,sub_eq_add_neg,←Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [rfPole_eval_deriv _ _ _ (hx m hm)]
  ring
private theorem finite_pf_deriv2 (R : ℚ[X]) (S : Finset ℕ) (c : ℕ→ℚ) (x : ℚ)
    (hx : ∀ m∈S,x+(m:ℚ)≠0) :
    rfEval (rfDeriv (rfDeriv (rfPoly R+∑ m∈S,rfPole (c m) m))) x=
      R.derivative.derivative.eval x+∑ m∈S,(2*c m)/(x+(m:ℚ))^3 := by
  have hr (m : ℕ) (hm : m∈S) : RFRegular x (rfDeriv (rfDeriv (rfPole (c m) m))) :=
    (rfPole_regular (c m) x m (hx m hm)).deriv.deriv
  have he : rfDeriv (rfPoly R+∑ m∈S,rfPole (c m) m)=
      rfPoly R.derivative+∑ m∈S,rfDeriv (rfPole (c m) m) := by
    rw [rfDeriv_add,rfDeriv_poly,rfDeriv_sum]
  have he2 : rfDeriv (rfDeriv (rfPoly R+∑ m∈S,rfPole (c m) m))=
      rfPoly R.derivative.derivative+∑ m∈S,rfDeriv (rfDeriv (rfPole (c m) m)) := by
    calc
      _=rfDeriv (rfPoly R.derivative+∑ m∈S,rfDeriv (rfPole (c m) m)) := congrArg rfDeriv he
      _=_ := by rw [rfDeriv_add,rfDeriv_poly,rfDeriv_sum]
  rw [he2,rfEval_add (RFRegular.poly x _) (RFRegular.sum S _ x hr),rfEval_poly,
    rfEval_sum S _ x hr]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  exact rfPole_eval_deriv2 _ _ _ (hx m hm)

private theorem rfPoly_Cq (q : ℚ) : rfPoly (C q)=algebraMap ℚ (RatFunc ℚ) q := by
  simpa [rfPoly] using (RatFunc.algebraMap_apply (K:=ℚ) q).symm
private theorem rfPoly_line (q : ℚ) :
    rfPoly (X+C q)=rfX+algebraMap ℚ (RatFunc ℚ) q := by
  calc
    _=rfPoly X+rfPoly (C q) := by simp only [rfPoly,map_add]
    _=_ := by rw [rfPoly_Cq];rfl
private theorem times_pole (a c : ℚ) (m : ℕ) :
    (rfX+rfPoly (C a))*rfPole c m=rfPoly (C c)+rfPole (c*(a-(m:ℚ))) m := by
  have hn : rfPoly (X+C (m:ℚ))≠0 := RatFunc.algebraMap_ne_zero (Polynomial.monic_X_add_C _).ne_zero
  rw [rfPoly_line] at hn
  simp only [rfPole,rfPoly_line,rfPoly_Cq] at hn ⊢
  simp only [map_mul,map_sub]
  field_simp [hn]
  <;> ring
private theorem times_finite_pf (R : ℚ[X]) (S : Finset ℕ) (c : ℕ→ℚ) (a : ℚ) :
    (rfX+rfPoly (C a))*(rfPoly R+∑ m∈S,rfPole (c m) m)=
      rfPoly ((X+C a)*R+C (∑ m∈S,c m))+
        ∑ m∈S,rfPole (c m*(a-(m:ℚ))) m := by
  rw [mul_add,Finset.mul_sum]
  have hpoly : (rfX+rfPoly (C a))*rfPoly R=rfPoly ((X+C a)*R) := by
    simp only [rfX,rfPoly,map_add,map_mul]
  rw [hpoly]
  simp_rw [times_pole]
  rw [Finset.sum_add_distrib]
  have hc : (∑ m∈S,rfPoly (C (c m)))=rfPoly (C (∑ m∈S,c m)) := by
    simp only [rfPoly,map_sum]
  rw [hc]
  simp only [rfPoly,map_add]
  ring
private theorem times_finite_pf_pole (R : ℚ[X]) (S : Finset ℕ) (c : ℕ→ℚ) (t : ℕ) (ht : t∈S) :
    (rfX+rfPoly (C (t:ℚ)))*(rfPoly R+∑ m∈S,rfPole (c m) m)=
      rfPoly ((X+C (t:ℚ))*R+C (∑ m∈S,c m))+
        ∑ m∈S.erase t,rfPole (c m*((t:ℚ)-m)) m := by
  rw [times_finite_pf]
  congr 1
  have he : rfPole (c t*((t:ℚ)-t)) t=0 := by
    simp only [sub_self,mul_zero,rfPole,map_zero,rfPoly,zero_div]
  have hs:=Finset.sum_erase_add S (fun m=>rfPole (c m*((t:ℚ)-m)) m) ht
  rw [he,add_zero] at hs
  exact hs.symm

private theorem finite_pf_pole_removed (R : ℚ[X]) (S : Finset ℕ) (c : ℕ→ℚ) (t : ℕ) (ht : t∈S) :
    rfEval (rfDeriv (rfDeriv ((rfX+rfPoly (C (t:ℚ)))*(rfPoly R+∑ m∈S,rfPole (c m) m)))) (-(t:ℚ))/2=
      R.derivative.eval (-(t:ℚ))-∑ m∈S.erase t,c m/((m:ℚ)-t)^2 := by
  classical
  rw [times_finite_pf_pole R S c t ht]
  have hx (m : ℕ) (hm : m∈S.erase t) : -(t:ℚ)+(m:ℚ)≠0 := by
    have hn : m≠t := (Finset.mem_erase.mp hm).1
    have hmt : (m:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    simpa only [sub_eq_add_neg,add_comm] using hmt
  rw [finite_pf_deriv2 _ (S.erase t) (fun m=>c m*((t:ℚ)-m)) (-(t:ℚ)) hx]
  have hpoly : (((X+C (t:ℚ))*R+C (∑ m∈S,c m)).derivative.derivative).eval (-(t:ℚ))=
      2*R.derivative.eval (-(t:ℚ)) := by
    simp only [Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_X,
      Polynomial.derivative_C,add_zero,zero_add,mul_one,one_mul,zero_mul,mul_zero,
      Polynomial.derivative_one,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_C,neg_add_cancel,Polynomial.eval_zero,zero_add,zero_mul]
    ring
  rw [hpoly]
  calc
    _=R.derivative.eval (-(t:ℚ))+
        ∑ m∈S.erase t,((2*(c m*((t:ℚ)-m)))/(-(t:ℚ)+m)^3)/2 := by
      rw [add_div,Finset.sum_div]
      ring
    _=R.derivative.eval (-(t:ℚ))-∑ m∈S.erase t,c m/((m:ℚ)-t)^2 := by
      rw [sub_eq_add_neg,←Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      have hd : (m:ℚ)-t≠0 := sub_ne_zero.mpr (by exact_mod_cast (Finset.mem_erase.mp hm).1)
      rw [show -(t:ℚ)+(m:ℚ)=(m:ℚ)-t by ring]
      field_simp [hd]
      <;> ring
private theorem sum_split_pole (S : Finset ℕ) (f : ℕ→ℚ) (t : ℕ) (ht : f t=0) :
    (∑ m∈S,f m)=(∑ m∈S.filter (fun m=>m<t),f m)+(∑ m∈S.filter (fun m=>t<m),f m) := by
  classical
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rcases lt_trichotomy m t with h|h|h
  · simp [h,not_lt_of_ge (le_of_lt h)]
  · subst m
    simp [ht]
  · simp [h,not_lt_of_ge (le_of_lt h)]

private theorem weight_partial_fractions (A : TypeKey) (g : ℚ[X]) :
    rfPoly g*weight A=rfPoly (polyPart A g)+
      ∑ m∈poleSet A,rfPole (residue A m*g.eval (-(m:ℚ))) m := by
  have hf : rfPoly g*weight A=rfPoly (weightNum A*g)/rfPoly (poleProd (poleSet A)) := by
    simp only [weight,weightDen,poleProd,rfPoly,map_mul,div_eq_mul_inv]
    ring
  rw [hf,pole_fraction_decomposition]
  change rfPoly (polyPart A g)+(∑ m∈poleSet A,rfPole (poleCoeff (weightNum A*g) (poleSet A) m) m)=_
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (fun c:ℚ=>rfPole c m)
  simp only [poleCoeff,poleProd,residue,weightDen,Polynomial.eval_mul,div_eq_mul_inv]
  ring
theorem moment_at_infinity (A : TypeKey) (g : ℚ[X]) :
  Oge (atInf (momentRF A g)) 0 ∧
    ∀ t : ℕ,(atInf (momentRF A g)).coeff (t:ℤ)=
      -(∑ m∈(poleSet A).filter (fun m=>m<t),
        residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2)-
      if t∈poleSet A then
        rfEval (rfDeriv (rfDeriv ((rfX+rfPoly (C (t:ℚ)))*rfPoly g*weight A))) (-(t:ℚ))/2
      else rfEval (rfDeriv (rfPoly g*weight A)) (-(t:ℚ)) := by
  refine ⟨(moment_inf_finite_coeff A g).1,?_⟩
  intro t
  rw [(moment_inf_finite_coeff A g).2 t]
  have hpart:=sum_split_pole (poleSet A)
    (fun m=>residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2) t (by simp)
  by_cases ht : t∈poleSet A
  · rw [if_pos ht]
    have hd:=finite_pf_pole_removed (polyPart A g) (poleSet A)
      (fun m=>residue A m*g.eval (-(m:ℚ))) t ht
    have herase : (∑ m∈(poleSet A).erase t,residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2)=
        ∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2 := by
      have hz : residue A t*g.eval (-(t:ℚ))/((t:ℚ)-t)^2=0 := by
        rw [sub_self]
        norm_num
      have hs:=Finset.sum_erase_add (poleSet A)
        (fun m=>residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2) ht
      rw [hz,add_zero] at hs
      exact hs
    have hD : rfEval (rfDeriv (rfDeriv ((rfX+rfPoly (C (t:ℚ)))*rfPoly g*weight A))) (-(t:ℚ))/2=
        (polyPart A g).derivative.eval (-(t:ℚ))-
          ∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2 := by
      rw [mul_assoc,weight_partial_fractions A g]
      simpa only [herase] using hd
    rw [hD,hpart]
    ring
  · rw [if_neg ht]
    have hx (m : ℕ) (hm : m∈poleSet A) : -(t:ℚ)+(m:ℚ)≠0 := by
      have hmt : m≠t := by intro he;subst m;exact ht hm
      have hh : (m:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hmt)
      simpa only [sub_eq_add_neg,add_comm] using hh
    have hd:=finite_pf_deriv (polyPart A g) (poleSet A)
      (fun m=>residue A m*g.eval (-(m:ℚ))) (-(t:ℚ)) hx
    have hD : rfEval (rfDeriv (rfPoly g*weight A)) (-(t:ℚ))=
        (polyPart A g).derivative.eval (-(t:ℚ))-
          ∑ m∈poleSet A,residue A m*g.eval (-(m:ℚ))/((m:ℚ)-t)^2 := by
      rw [weight_partial_fractions A g]
      simpa only [sub_eq_add_neg,add_comm] using hd
    rw [hD,hpart]
    ring
#print axioms moment_at_infinity
#print axioms rfDeriv_eq_audited
#print axioms rfEval_eq_audited
end
end CatalanCore.Li2.NVMod
