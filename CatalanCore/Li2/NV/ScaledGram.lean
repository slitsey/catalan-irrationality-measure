module
public import CatalanCore.Li2.NV.ReductionData
public import CatalanCore.Li2.NV.Thresholds
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset Matrix
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
private theorem parameterG_affine_power (w q s : ℚ) (j : ℕ) :
    Port.Li2.parameterG w ((C q*X-C s)^j)=
      ∑ i∈Finset.range (j+1),(Nat.choose j i:ℚ)*(-s)^(j-i)*q^i*
        Port.Li2.parameterMoment w i := by
  have hp : (C q*X-C s)^j=(∑ i∈Finset.range (j+1),
      C ((Nat.choose j i:ℚ)*(-s)^(j-i)*q^i)*X^i) := by
    rw [sub_eq_add_neg,add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    have hn : (Nat.choose j i:ℚ[X])=C (Nat.choose j i:ℚ):=by simp
    simp only [mul_pow,←map_neg,←map_pow,hn,←map_mul]
    simp only [map_mul,map_pow,map_neg]
    ring
  rw [hp,Port.Li2.parameterG_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Port.Li2.parameterG_C_mul_X_pow w _ i

private theorem polynomial_G_distribution (z : ℚ) (hz : z≠0) (h1 : z≠1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hw : z^ℓ≠1) (P : ℚ[X]) :
    Port.Li2.parameterG z P=∑s : Fin ℓ,z^(-(s:ℤ))*
      Port.Li2.parameterG (z^ℓ) (P.comp (C (ℓ:ℚ)*X-C (s:ℚ))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ=>
    rw [Port.Li2.parameterG_add,hP,hQ]
    simp only [add_comp,Port.Li2.parameterG_add,mul_add,Finset.sum_add_distrib]
  | monomial j a=>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp only [mul_comp,C_comp,pow_comp,X_comp,Port.Li2.parameterG_C_mul]
    have hg : Port.Li2.parameterG z (X^j)=Port.Li2.parameterMoment z j:=by
      simpa using Port.Li2.parameterG_C_mul_X_pow z 1 j
    rw [hg]
    have hh:=li_distribution z hz h1 ℓ hw j
    simp_rw [liNeg_eq_parameterMoment z h1,liNeg_eq_parameterMoment (z^ℓ) hw] at hh
    rw [hh,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [parameterG_affine_power]
    ring
private theorem simple_pole_data (j : ℕ) :
    let F:=(rfX+rfPoly (C (j:ℚ)))⁻¹
    pp F=0 ∧ poleIndices F={j} ∧ poleRes F j=1 := by
  classical
  let F:=(rfX+rfPoly (C (j:ℚ)))⁻¹
  have hF : F=rfPoly 1/rfPoly (poleProd {j}):=by
    simp [F,rfX,rfPoly,poleProd,map_add]
  have hc:=fraction_coefficients 1 {j}
  have hq : (1:ℚ[X]) /ₘ poleProd {j}=0:=by
    simp only [poleProd,Finset.prod_singleton]
    rw [Polynomial.divByMonic_eq_zero_iff (monic_X_add_C _),degree_one,degree_X_add_C]
    norm_num
  have hr : poleCoeff 1 {j} j=1:=by simp [poleCoeff,poleProd]
  have hdiv : F.denom∣poleProd {j}:=by rw [hF];exact RatFunc.denom_div_dvd _ _
  obtain ⟨hD,hI⟩:=canonical_poles F {j} hdiv
  have hsub : poleIndices F⊆{j}:=by rw [hI];exact Finset.filter_subset _ _
  have he : (if j∈poleIndices F then poleRes F j else 0)=1:=by
    rw [hF]
    simpa only [hr] using hc.2 j (Finset.mem_singleton_self j)
  have hm : j∈poleIndices F:=by
    by_contra hn
    simp [hn] at he
  have hset : poleIndices F={j}:=Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hm)
  refine ⟨?_,hset,?_⟩
  · change pp F=0
    rw [hF,hc.1,hq]
  · simpa only [if_pos hm] using he
private theorem simple_pole_values (z x : ℚ) (ℓ j : ℕ) [Fact ℓ.Prime]
    (ξ : Padic ℓ) (s : Fin ℓ) :
    li2Lambda z x ((rfX+rfPoly (C (j:ℚ)))⁻¹)=
      (j:ℚ)*z^(-(j:ℤ))*(x-tauK z j) ∧
    localClass z ℓ s ξ ((rfX+rfPoly (C (j:ℚ)))⁻¹)=
      (j:Padic ℓ)*(if j%ℓ=s.val then
        (z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
          ((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) (j/ℓ):ℚ))
        else (z:Padic ℓ)^(-(s:ℤ))*E z ℓ ((j:ℤ)-s.val)) := by
  obtain ⟨hp,hI,hr⟩:=simple_pole_data j
  constructor
  · rw [li2Lambda,hp,hI,Finset.sum_singleton,hr]
    simp
  · rw [localClass,hp,hI,Finset.sum_singleton,hr]
    simp
private theorem parameterU_formula (z : ℚ) (hz : z≠1) (P : ℚ[X]) :
    Port.Li2.parameterG z (X*P).derivative=
      ∑ i∈Finset.range (P.natDegree+1),(i+1:ℚ)*P.coeff i*liNeg i z := by
  let f : ℕ→ℚ→ℚ:=fun i a=>(i+1:ℚ)*a*liNeg i z
  have hpoly : ∀ P : ℚ[X],Port.Li2.parameterG z (X*P).derivative=P.sum f := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      rw [mul_add,derivative_add,Port.Li2.parameterG_add,hP,hQ]
      symm
      exact Polynomial.sum_add_index _ _ _ (fun i=>by simp [f]) (fun i a b=>by dsimp [f];ring)
    | monomial i a =>
      simp only [X_mul_monomial,derivative_monomial_succ,Port.Li2.parameterG_monomial]
      rw [Polynomial.sum_monomial_index a f (by simp [f])]
      dsimp [f]
      rw [liNeg_eq_parameterMoment z hz]
      ring
  rw [hpoly]
  simpa only [f] using (Polynomial.sum_over_range P (f:=f) (fun i=>by simp [f]))

private theorem polynomial_li_sum (w : ℚ) (hw : w≠1) (P : ℚ[X]) :
    (∑i∈Finset.range (P.natDegree+1),P.coeff i*liNeg i w)=Port.Li2.parameterG w P := by
  simp_rw [liNeg_eq_parameterMoment w hw]
  unfold Port.Li2.parameterG
  exact (P.sum_over_range (f:=fun n a=>a*Port.Li2.parameterMoment w n) (fun n=>by simp)).symm
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
private theorem parameter_hypotheses (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) :
    z≠0 ∧ Port.Li2.VG ℓ (z^ℓ) 0 ∧ Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0 ∧ z^ℓ≠1 :=
  Port.Unified.Proofs.Hermite.parameterPoleHypotheses_of_hunit z
    ⟨rational_unit_of_norm ℓ z hz,rational_unit_of_norm ℓ (1-z) h1⟩

private theorem polynomial_local_distribution (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (P : ℚ[X]) :
    (∑i∈Finset.range (P.natDegree+1),(i+1:Padic ℓ)*(P.coeff i:Padic ℓ)*(liNeg i z:ℚ))=
      ∑s : Fin ℓ,(z:Padic ℓ)^(-(s.val:ℤ))*
        ∑i∈Finset.range (((X*P).derivative.comp (C (-(s:ℚ))+C (ℓ:ℚ)*X)).natDegree+1),
          (((X*P).derivative.comp (C (-(s:ℚ))+C (ℓ:ℚ)*X)).coeff i:Padic ℓ)*(liNeg i (z^ℓ):ℚ) := by
  have hu:=rational_unit_of_norm ℓ z hz
  have hv:=rational_unit_of_norm ℓ (1-z) h1
  have hw : z≠1:=by intro he;apply hv.1;simp [he]
  have hp:=(parameter_hypotheses z ℓ hz h1).2.2.2
  have hh:=polynomial_G_distribution z hu.1 hw ℓ hp (X*P).derivative
  rw [parameterU_formula z hw P] at hh
  have ha (s : Fin ℓ) : C (ℓ:ℚ)*X-C (s:ℚ)=C (-(s:ℚ))+C (ℓ:ℚ)*X:=by simp [sub_eq_add_neg,add_comm]
  simp_rw [ha,←polynomial_li_sum (z^ℓ) hp] at hh
  have hc:=congrArg (fun q : ℚ=>(q:Padic ℓ)) hh
  simpa only [Rat.cast_sum,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_zpow] using hc
private theorem lambda_local_distribution (z x : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (L : PadicInt ℓ) (hL : ∀j≥1,T z ℓ j=(L:Padic ℓ))
    (F : RatFunc ℚ) (hpos : ∀j∈poleIndices F,0<j) :
    (li2Lambda z x F:Padic ℓ)=∑s : Fin ℓ,localClass z ℓ s ((x:Padic ℓ)-L) F := by
  classical
  have hp (j : ℕ) (hj : j∈poleIndices F) :
      (j:Padic ℓ)*(z:Padic ℓ)^(-(j:ℤ))*((x:Padic ℓ)-(tauK z j:ℚ))=
        ∑s : Fin ℓ,(j:Padic ℓ)*(if j%ℓ=s.val then
          (z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
            ((ℓ:Padic ℓ)^2*((x:Padic ℓ)-L)-(tauK (z^ℓ) (j/ℓ):ℚ))
          else (z:Padic ℓ)^(-(s:ℤ))*E z ℓ ((j:ℤ)-s.val)):=by
    have hh:=decompose_simple_pole z x ℓ j hz h1 (hpos j hj) L hL
    rw [(simple_pole_values z x ℓ j ((x:Padic ℓ)-L) ⟨0,(Fact.out : ℓ.Prime).pos⟩).1] at hh
    simp_rw [fun s=>(simple_pole_values z x ℓ j ((x:Padic ℓ)-L) s).2] at hh
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_zpow,Rat.cast_sub] using hh
  unfold li2Lambda localClass
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_zpow,Rat.cast_sub]
  rw [Finset.sum_add_distrib,polynomial_local_distribution z ℓ hz h1 (pp F)]
  congr 1
  calc
    _=∑j∈poleIndices F,(poleRes F j:Padic ℓ)*
        ((j:Padic ℓ)*(z:Padic ℓ)^(-(j:ℤ))*((x:Padic ℓ)-(tauK z j:ℚ))):=by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _=∑j∈poleIndices F,(poleRes F j:Padic ℓ)*
      ∑s : Fin ℓ,(j:Padic ℓ)*(if j%ℓ=s.val then
          (z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
            ((ℓ:Padic ℓ)^2*((x:Padic ℓ)-L)-(tauK (z^ℓ) (j/ℓ):ℚ))
          else (z:Padic ℓ)^(-(s:ℤ))*E z ℓ ((j:ℤ)-s.val)):=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hp j hj]
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro j hj
      ring
private theorem pairRF_fraction (n ℓ : ℕ) (P Q : Ix n ℓ) :
    pairRF n ℓ P Q=rfPoly ((Port.Li2.D n)^3*(crtE n ℓ P*crtE n ℓ Q))/rfPoly (Port.Li2.D (4*n)) := by
  unfold pairRF W rfPoly
  simp only [map_mul,map_pow]
  ring

private theorem pairRF_poles_positive (n ℓ : ℕ) (P Q : Ix n ℓ) :
    ∀j∈poleIndices (pairRF n ℓ P Q),0<j := by
  classical
  let F:=pairRF n ℓ P Q
  let S:=Finset.Icc 1 (4*n)
  have hdiv : F.denom∣poleProd S:=by
    rw [show F=rfPoly ((Port.Li2.D n)^3*(crtE n ℓ P*crtE n ℓ Q))/rfPoly (poleProd S) from pairRF_fraction n ℓ P Q]
    exact RatFunc.denom_div_dvd _ _
  have hI:=(canonical_poles F S hdiv).2
  intro j hj
  change j∈poleIndices F at hj
  rw [hI] at hj
  have hi:=Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  omega
private theorem gram_local_distribution (z x : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (L : PadicInt ℓ) (hL : ∀j≥1,T z ℓ j=(L:Padic ℓ)) (P Q : Ix n ℓ) :
    (G z n ℓ x P Q:Padic ℓ)=∑s : Fin ℓ,localClass z ℓ s ((x:Padic ℓ)-L) (pairRF n ℓ P Q) := by
  have hu:=rational_unit_of_norm ℓ z hz
  have hv:=rational_unit_of_norm ℓ (1-z) h1
  have hw : z≠1:=by intro he;apply hv.1;simp [he]
  change (li2Lam z n x (crtE n ℓ P*crtE n ℓ Q):Padic ℓ)=_
  rw [(lam_linear_and_F0 z x hu.1 hw n).2]
  exact lambda_local_distribution z x ℓ hz h1 L hL (pairRF n ℓ P Q) (pairRF_poles_positive n ℓ P Q)
private theorem exists_nonnegative_shift {ι : Type*} [Fintype ι]
    (a b : ι→ℤ) : ∃ (Ξ : ℕ) (ex ey : ι→ℕ),
      ∀i,(ex i:ℤ)=a i+Ξ ∧ (ey i:ℤ)=b i+Ξ := by
  classical
  let Ξ:=∑i,((a i).natAbs+(b i).natAbs)
  have hnon (i : ι) : 0≤a i+(Ξ:ℤ) ∧ 0≤b i+(Ξ:ℤ):=by
    have hs : (a i).natAbs+(b i).natAbs≤Ξ:=
      Finset.single_le_sum (f:=fun j : ι=>(a j).natAbs+(b j).natAbs) (fun j hj=>Nat.zero_le _) (Finset.mem_univ i)
    have ha : -(a i)≤((a i).natAbs:ℤ):=by rw [Int.natCast_natAbs];exact neg_le_abs _
    have hb : -(b i)≤((b i).natAbs:ℤ):=by rw [Int.natCast_natAbs];exact neg_le_abs _
    omega
  refine ⟨Ξ,(fun i=>(a i+(Ξ:ℤ)).toNat),(fun i=>(b i+(Ξ:ℤ)).toNat),?_⟩
  intro i
  exact ⟨Int.toNat_of_nonneg (hnon i).1,Int.toNat_of_nonneg (hnon i).2⟩
private theorem exists_gram_exponents (n ℓ : ℕ) :
    ∃ (Ξ : ℕ) (ex ey : Ix n ℓ→ℕ),∀P,
      (ex P:ℤ)=(P.2:ℤ)+(nu n ℓ P.1-nu n ℓ P.1%2)/2+Ξ ∧
      (ey P:ℤ)=(P.2:ℤ)+(nu n ℓ P.1+nu n ℓ P.1%2)/2+Ξ :=
  exists_nonnegative_shift _ _

private def entryExponent (n ℓ : ℕ) (P Q : Ix n ℓ) : ℤ:=
  (P.2:ℤ)+(nu n ℓ P.1-nu n ℓ P.1%2)/2+
    (Q.2:ℤ)+(nu n ℓ Q.1+nu n ℓ Q.1%2)/2
private theorem entryExponent_slack (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) :
    (((nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q-entryExponent n ℓ P Q):ℤ):ℚ)=
      slack n ℓ s P Q+(((nu n ℓ P.1%2:ℤ):ℚ)-((nu n ℓ Q.1%2:ℤ):ℚ))/2 := by
  have hp : nu n ℓ P.1%2+2*(nu n ℓ P.1/2)=nu n ℓ P.1:=by omega
  have hq : nu n ℓ Q.1%2+2*(nu n ℓ Q.1/2)=nu n ℓ Q.1:=by omega
  have hrow : (nu n ℓ P.1-nu n ℓ P.1%2)/2=nu n ℓ P.1/2:=by omega
  have hcol : (nu n ℓ Q.1+nu n ℓ Q.1%2)/2=nu n ℓ Q.1/2+nu n ℓ Q.1%2:=by omega
  unfold entryExponent slack pi
  rw [hrow,hcol]
  push_cast
  have hp' : ((nu n ℓ P.1%2:ℤ):ℚ)+2*((nu n ℓ P.1/2:ℤ):ℚ)=(nu n ℓ P.1:ℚ):=by exact_mod_cast hp
  have hq' : ((nu n ℓ Q.1%2:ℤ):ℚ)+2*((nu n ℓ Q.1/2:ℤ):ℚ)=(nu n ℓ Q.1:ℚ):=by exact_mod_cast hq
  linear_combination -(hp'+hq')/2
private theorem entryExponent_bounds (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (P Q : Ix n ℓ) :
    entryExponent n ℓ P Q≤nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q ∧
      (nu n ℓ P.1%2≠0 → nu n ℓ Q.1%2=0 →
        entryExponent n ℓ P Q+1≤nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q) ∧
      (nu n ℓ P.1%2=nu n ℓ Q.1%2 →
        (nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q=entryExponent n ℓ P Q ↔
          (s=P.1∧s=Q.1)∨ExceptionalSlack n ℓ s P Q)) := by
  have ht:=threshold n ℓ hR s P Q
  have he:=entryExponent_slack n ℓ s P Q
  have hrP : 0≤nu n ℓ P.1%2∧nu n ℓ P.1%2<2:=⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  have hrQ : 0≤nu n ℓ Q.1%2∧nu n ℓ Q.1%2<2:=⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  refine ⟨?_,?_,?_⟩
  · have hp' : (-1:ℚ)<((nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q-entryExponent n ℓ P Q:ℤ):ℚ):=by
      have hP : (0:ℚ)≤(nu n ℓ P.1%2:ℤ):=by exact_mod_cast hrP.1
      have hQ : ((nu n ℓ Q.1%2:ℤ):ℚ)≤1:=by exact_mod_cast (show nu n ℓ Q.1%2≤1 by omega)
      linarith [ht.1]
    have hi : -1<nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q-entryExponent n ℓ P Q:=by exact_mod_cast hp'
    omega
  · intro hP hQ
    have hp : nu n ℓ P.1%2=1:=by omega
    rw [hp,hQ] at he
    have hh : (0:ℚ)<((nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q-entryExponent n ℓ P Q:ℤ):ℚ):=by norm_num at he ⊢;linarith [ht.1]
    have hi : 0<nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q-entryExponent n ℓ P Q:=by exact_mod_cast hh
    omega
  · intro hpar
    rw [hpar,sub_self,zero_div,add_zero] at he
    rw [←ht.2.1]
    constructor
    · intro hx
      rw [hx,sub_self,Int.cast_zero] at he
      exact he.symm
    · intro hx
      rw [hx] at he
      have hh : nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q-entryExponent n ℓ P Q=0:=by exact_mod_cast he
      omega
private theorem Vge_mul_levels (ℓ : ℕ) [Fact ℓ.Prime] (x y : Padic ℓ) (e f : ℤ)
    (hx : Vge ℓ x e) (hy : Vge ℓ y f) : Vge ℓ (x*y) (e+f) := by
  have hp : (0:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).pos
  unfold Vge at hx hy ⊢
  rw [norm_mul]
  calc
    _≤(ℓ:ℝ)^(-(e:ℝ))*(ℓ:ℝ)^(-(f:ℝ)):=mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _=_:=by rw [←Real.rpow_add hp];congr 1;push_cast;ring
private theorem Vge_prime_power (ℓ : ℕ) [Fact ℓ.Prime] (e : ℤ) :
    Vge ℓ ((ℓ:Padic ℓ)^e) e := by
  unfold Vge
  rw [←Int.cast_neg,Real.rpow_intCast,Padic.norm_p_zpow]
private theorem Vge_unit_scalar (ℓ : ℕ) [Fact ℓ.Prime] (u x : Padic ℓ)
    (hu : Unit ℓ u) (e : ℤ) (hx : Vge ℓ x e) : Vge ℓ (u*x) e := by
  unfold Vge
  rw [norm_mul,hu,one_mul]
  exact hx
private theorem Vge_scaled (ℓ : ℕ) [Fact ℓ.Prime] (u x : Padic ℓ)
    (hu : Unit ℓ u) (e f : ℤ) (hx : Vge ℓ x f) :
    Vge ℓ (u*(ℓ:Padic ℓ)^e*x) (e+f) := by
  rw [mul_assoc]
  exact Vge_unit_scalar ℓ u _ hu (e+f) (Vge_mul_levels ℓ _ _ e f (Vge_prime_power ℓ e) hx)
private theorem scaled_coordinate_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) : Intg ℓ ((ℓ:Padic ℓ)^2*ξ) := by
  have hp : (0:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).pos
  have hξ' : ‖ξ‖≤(ℓ:ℝ):=by
    simpa only [Vge,Int.cast_neg,Int.cast_one,neg_neg,Real.rpow_one] using hξ
  unfold Intg
  rw [norm_mul,norm_pow,Padic.norm_p]
  calc
    (ℓ:ℝ)⁻¹^2*‖ξ‖≤(ℓ:ℝ)⁻¹^2*ℓ:=mul_le_mul_of_nonneg_left hξ' (sq_nonneg _)
    _=(ℓ:ℝ)⁻¹:=by field_simp <;> ring
    _≤1:=(inv_le_one₀ hp).mpr (by exact_mod_cast (Fact.out : ℓ.Prime).one_le)

private theorem Vge_mono (ℓ : ℕ) [Fact ℓ.Prime] (x : Padic ℓ) (e f : ℤ)
    (h : f≤e) (hx : Vge ℓ x e) : Vge ℓ x f := by
  have hp : (1:ℝ)≤ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).one_le
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le hp (by exact_mod_cast neg_le_neg h))
private theorem coordinate_sub_integral_bound (ℓ : ℕ) [Fact ℓ.Prime]
    (x : Padic ℓ) (hx : Vge ℓ x (-1)) (L : PadicInt ℓ) : Vge ℓ (x-L) (-1) := by
  have hnorm : ‖x‖≤(ℓ:ℝ):=by
    simpa only [Vge,Int.cast_neg,Int.cast_one,neg_neg,Real.rpow_one] using hx
  have hL : ‖(L:Padic ℓ)‖≤(ℓ:ℝ):=(PadicInt.norm_le_one L).trans (by exact_mod_cast (Fact.out : ℓ.Prime).one_le)
  have hh:=(IsUltrametricDist.norm_add_le_max x (-(L:Padic ℓ))).trans (max_le hnorm (by simpa only [norm_neg] using hL))
  simpa only [sub_eq_add_neg,Vge,Int.cast_neg,Int.cast_one,neg_neg,Real.rpow_one] using hh
private def normalizedGram (z : ℚ) (n ℓ : ℕ) (x : ℚ) : Matrix (Ix n ℓ) (Ix n ℓ) ℚ:=
  fun P Q=>(ℓ:ℚ)^(-entryExponent n ℓ P Q)*G z n ℓ x P Q
private theorem normalized_local_bound (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1))
    (s : Fin ℓ) (P Q : Ix n ℓ) :
    Vge ℓ ((ℓ:Padic ℓ)^(-entryExponent n ℓ P Q)*localClass z ℓ s ξ (pairRF n ℓ P Q)) 0 ∧
      (nu n ℓ P.1%2≠0 → nu n ℓ Q.1%2=0 →
        Vge ℓ ((ℓ:Padic ℓ)^(-entryExponent n ℓ P Q)*localClass z ℓ s ξ (pairRF n ℓ P Q)) 1) := by
  obtain ⟨Ψ,hΨ,hf,hs,he,hv,hx,hSame,hTied⟩:=local_expansion z n ℓ hz h1 hR s P Q ξ hξ
  have hh:=Vge_mul_levels ℓ _ _ (-entryExponent n ℓ P Q)
    (nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q) (Vge_prime_power ℓ _) hv
  have hb:=entryExponent_bounds n ℓ hR s P Q
  constructor
  · exact Vge_mono ℓ _ _ 0 (by omega) hh
  · intro hP hQ
    exact Vge_mono ℓ _ _ 1 (by have h:=hb.2.1 hP hQ;omega) hh
private theorem normalized_gram_bound (z x : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (hx : Vge ℓ (x:Padic ℓ) (-1)) (P Q : Ix n ℓ) :
    Intg ℓ ((normalizedGram z n ℓ x P Q:ℚ):Padic ℓ) ∧
      (nu n ℓ P.1%2≠0 → nu n ℓ Q.1%2=0 →
        Vge ℓ ((normalizedGram z n ℓ x P Q:ℚ):Padic ℓ) 1) := by
  obtain ⟨L,hL⟩:=(regularization_constant z ℓ hz h1).2.2
  let ξ:=(x:Padic ℓ)-(L:Padic ℓ)
  have hξ : Vge ℓ ξ (-1):=coordinate_sub_integral_bound ℓ _ hx L
  have hsum : ((normalizedGram z n ℓ x P Q:ℚ):Padic ℓ)=
      ∑s : Fin ℓ,(ℓ:Padic ℓ)^(-entryExponent n ℓ P Q)*localClass z ℓ s ξ (pairRF n ℓ P Q):=by
    simp only [normalizedGram,Rat.cast_mul,Rat.cast_zpow,Rat.cast_natCast]
    rw [gram_local_distribution z x n ℓ hz h1 L hL P Q,Finset.mul_sum]
  rw [hsum]
  constructor
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
    intro s hs
    simpa only [Vge,Int.cast_zero,neg_zero,Real.rpow_zero] using
      (normalized_local_bound z n ℓ hz h1 hR ξ hξ s P Q).1
  · intro hP hQ
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro s hs
    exact (normalized_local_bound z n ℓ hz h1 hR ξ hξ s P Q).2 hP hQ

private theorem scaled_gram_integral_lift (z x : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (hx : Vge ℓ (x:Padic ℓ) (-1)) :
    ∃ (Ξ : ℕ) (ex ey : Ix n ℓ→ℕ) (Z : Matrix (Ix n ℓ) (Ix n ℓ) (Basic.LocRing ℓ)),
      (∀P,(ex P:ℤ)=(P.2:ℤ)+(nu n ℓ P.1-nu n ℓ P.1%2)/2+Ξ ∧
        (ey P:ℤ)=(P.2:ℤ)+(nu n ℓ P.1+nu n ℓ P.1%2)/2+Ξ) ∧
      (∀P Q,(ℓ:ℚ)^(2*Ξ)*G z n ℓ x P Q=(ℓ:ℚ)^(ex P)*(Z P Q:ℚ)*(ℓ:ℚ)^(ey Q)) ∧
      (∀P Q,(Z P Q:ℚ)=normalizedGram z n ℓ x P Q) ∧
      (∀P Q,nu n ℓ P.1%2≠0 → nu n ℓ Q.1%2=0 → Arith.Hybrid.redQ ℓ (Z P Q)=0) := by
  classical
  obtain ⟨Ξ,ex,ey,hE⟩:=exists_gram_exponents n ℓ
  let Z : Matrix (Ix n ℓ) (Ix n ℓ) (Basic.LocRing ℓ):=fun P Q=>
    ⟨normalizedGram z n ℓ x P Q,(rat_integral_iff_locRing ℓ _).mp
      (normalized_gram_bound z x n ℓ hz h1 hR hx P Q).1⟩
  refine ⟨Ξ,ex,ey,Z,hE,?_,?_,?_⟩
  · intro P Q
    have hp : (ℓ:ℚ)≠0:=by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hsum : (ex P:ℤ)+(ey Q:ℤ)=entryExponent n ℓ P Q+2*(Ξ:ℤ):=by
      rw [(hE P).1,(hE Q).2]
      unfold entryExponent
      ring
    have hpow : (ℓ:ℚ)^(ex P)*(ℓ:ℚ)^(ey Q)=
        (ℓ:ℚ)^(entryExponent n ℓ P Q+2*(Ξ:ℤ)):=by
      rw [←zpow_natCast,←zpow_natCast,←_root_.zpow_add₀ hp,hsum]
    have hcancel : (ℓ:ℚ)^(entryExponent n ℓ P Q+2*(Ξ:ℤ))*
        (ℓ:ℚ)^(-entryExponent n ℓ P Q)=(ℓ:ℚ)^(2*(Ξ:ℤ)):=by
      rw [←_root_.zpow_add₀ hp]
      congr 1
      ring
    have hNat : ((2*Ξ:ℕ):ℤ)=2*(Ξ:ℤ):=by push_cast;rfl
    have h2 : (ℓ:ℚ)^(2*Ξ:ℕ)=(ℓ:ℚ)^(2*(Ξ:ℤ)):=by rw [←hNat,zpow_natCast]
    change (ℓ:ℚ)^(2*Ξ)*G z n ℓ x P Q=(ℓ:ℚ)^(ex P)*normalizedGram z n ℓ x P Q*(ℓ:ℚ)^(ey Q)
    rw [h2,←hcancel,←hpow]
    unfold normalizedGram
    ring
  · intro P Q
    rfl
  · intro P Q hP hQ
    have hv : Vge ℓ (((locToPadicInt ℓ (Z P Q)):PadicInt ℓ):Padic ℓ) 1:=by
      change Vge ℓ ((normalizedGram z n ℓ x P Q:ℚ):Padic ℓ) 1
      exact (normalized_gram_bound z x n ℓ hz h1 hR hx P Q).2 hP hQ
    have hr:=reduce_eq_of_Vge ℓ (locToPadicInt ℓ (Z P Q)) 0
      (by simpa only [PadicInt.coe_zero,sub_zero] using hv)
    rw [map_zero,locToPadicInt_red] at hr
    exact hr

private theorem normalize_local_leading (ℓ : ℕ) [Fact ℓ.Prime] (x u a : Padic ℓ) (e v : ℤ)
    (he : e=v) (hx : Vge ℓ (x-u*(ℓ:Padic ℓ)^e*a) (e+1)) :
    Vge ℓ ((ℓ:Padic ℓ)^(-v)*x-u*a) 1 := by
  subst e
  have hp : (ℓ:Padic ℓ)≠0:=by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hc : (ℓ:Padic ℓ)^(-v)*(ℓ:Padic ℓ)^v=1:=by
    rw [←_root_.zpow_add₀ hp,neg_add_cancel,zpow_zero]
  have hh:=Vge_mul_levels ℓ ((ℓ:Padic ℓ)^(-v)) (x-u*(ℓ:Padic ℓ)^v*a)
    (-v) (v+1) (Vge_prime_power ℓ (-v)) hx
  have hlev : -v+(v+1)=1:=by ring
  rw [hlev] at hh
  have hv : (ℓ:Padic ℓ)^(-v)*(x-u*(ℓ:Padic ℓ)^v*a)=
      (ℓ:Padic ℓ)^(-v)*x-u*a:=by
    calc
      _=(ℓ:Padic ℓ)^(-v)*x-u*((ℓ:Padic ℓ)^(-v)*(ℓ:Padic ℓ)^v)*a:=by ring
      _=_:=by rw [hc];ring
  rw [hv] at hh
  exact hh
private theorem nat_unit_norm (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (hs : s.val≠0) :
    ‖(s.val:PadicInt ℓ)‖=1 := by
  have hn : ¬ℓ∣s.val:=Nat.not_dvd_of_pos_of_lt (by omega) s.isLt
  exact le_antisymm (PadicInt.norm_le_one _)
    (le_of_not_gt (by rwa [PadicInt.norm_natCast_lt_one_iff]))
private theorem reduce_inv_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) (hx : ‖x‖=1) :
    reduceInt ℓ x.inv=(reduceInt ℓ x)⁻¹ := by
  have hm:=congrArg (reduceInt ℓ) (PadicInt.mul_inv hx)
  simp only [map_mul,map_one] at hm
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)
private theorem coe_inv_of_unit (ℓ : ℕ) [Fact ℓ.Prime] (x : PadicInt ℓ) (hx : ‖x‖=1) :
    ((x.inv:PadicInt ℓ):Padic ℓ)=(x:Padic ℓ)⁻¹ := by
  have hm:=congrArg (fun y : PadicInt ℓ=>(y:Padic ℓ)) (PadicInt.mul_inv hx)
  simp only [PadicInt.coe_mul,PadicInt.coe_one] at hm
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)
private def S0integral {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ) : PadicInt ℓ:=
  ∑s : Fin ℓ,if s.val∈Cset n ℓ then R.units s*(s.val:PadicInt ℓ).inv^2 else 0
private theorem S0integral_red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime] (R : ReductionData z n ℓ) :
    reduceInt ℓ (S0integral R)=S0red R := by
  classical
  unfold S0integral S0red
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hC : s.val∈Cset n ℓ
  · have hsn : s.val≠0:=by have hi:=Finset.mem_Ioc.mp hC;omega
    rw [if_pos hC,if_pos hC,map_mul,map_pow,reduce_inv_of_unit ℓ _ (nat_unit_norm ℓ s hsn)]
    simp only [map_natCast,redU,div_eq_mul_inv,inv_pow]
  · simp only [if_neg hC,map_zero]
private def diagonalIntegral {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (P Q : Ix n ℓ) : PadicInt ℓ:=
  if P.1=Q.1 then
    R.units P.1*R.moments (classKey n ℓ P.1) (P.2.val+Q.2.val)+
      if P.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ then
        S0integral R*R.moments (keyC n ℓ) (2*mC n ℓ) else 0
  else if P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ then
    -(R.units P.1*(P.1.val:PadicInt ℓ).inv)*R.moments (keyC n ℓ) (P.2.val+mC n ℓ)
  else if Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ then
    -(R.units Q.1*(Q.1.val:PadicInt ℓ).inv)*R.moments (keyC n ℓ) (Q.2.val+mC n ℓ)
  else 0
private theorem diagonalIntegral_red {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (P Q : Ix n ℓ) :
    reduceInt ℓ (diagonalIntegral R P Q)=expectedDiagonal R P Q := by
  classical
  unfold diagonalIntegral expectedDiagonal
  by_cases hPQ : P.1=Q.1
  · simp only [if_pos hPQ,map_add,map_mul]
    congr 1
    split_ifs <;> simp only [map_mul,S0integral_red,map_zero,redMoment]
  · simp only [if_neg hPQ]
    by_cases hC0 : P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ
    · have hn : P.1.val≠0:=by have hi:=Finset.mem_Ioc.mp hC0.1;omega
      simp only [if_pos hC0,map_mul,map_neg,reduce_inv_of_unit ℓ _ (nat_unit_norm ℓ P.1 hn),
        map_natCast,redU,redMoment,div_eq_mul_inv,inv_neg,neg_mul,mul_neg]
    · simp only [if_neg hC0]
      by_cases h0C : Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ
      · have hn : Q.1.val≠0:=by have hi:=Finset.mem_Ioc.mp h0C.1;omega
        simp only [if_pos h0C,map_mul,map_neg,reduce_inv_of_unit ℓ _ (nat_unit_norm ℓ Q.1 hn),
          map_natCast,redU,redMoment,div_eq_mul_inv,inv_neg,neg_mul,mul_neg]
      · simp only [if_neg h0C,map_zero]

private def classIntegral {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ) : PadicInt ℓ:=
  (if P.1=Q.1∧s=P.1 then R.units s*R.moments (classKey n ℓ s) (P.2.val+Q.2.val) else 0)+
  (if (P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ)∧s=P.1 then
    -(R.units s*(s.val:PadicInt ℓ).inv)*R.moments (keyC n ℓ) (P.2.val+mC n ℓ) else 0)+
  (if (Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ)∧s=Q.1 then
    -(R.units s*(s.val:PadicInt ℓ).inv)*R.moments (keyC n ℓ) (Q.2.val+mC n ℓ) else 0)+
  (if (P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ)∧s.val∈Cset n ℓ then
    R.units s*(s.val:PadicInt ℓ).inv^2*R.moments (keyC n ℓ) (2*mC n ℓ) else 0)
private theorem classIntegral_sum {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (P Q : Ix n ℓ) :
    (∑s : Fin ℓ,classIntegral R s P Q)=diagonalIntegral R P Q := by
  classical
  have hsingle (p : Fin ℓ) (H : Prop) [Decidable H] (f : Fin ℓ→PadicInt ℓ) :
      (∑s : Fin ℓ,if H∧s=p then f s else 0)=if H then f p else 0:=by
    by_cases h : H <;> simp [h,Finset.sum_ite_eq']
  unfold classIntegral
  simp only [Finset.sum_add_distrib]
  rw [hsingle,hsingle,hsingle]
  have hcorner : (∑s : Fin ℓ,if (P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ)∧s.val∈Cset n ℓ then
      R.units s*(s.val:PadicInt ℓ).inv^2*R.moments (keyC n ℓ) (2*mC n ℓ) else 0)=
      if P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ then
        S0integral R*R.moments (keyC n ℓ) (2*mC n ℓ) else 0:=by
    by_cases h : P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ
    · simp only [h,true_and,ite_true,S0integral,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> simp
    · simp only [h,false_and,ite_false,Finset.sum_const_zero]
  rw [hcorner]
  have hCne (s : Fin ℓ) (hs : s.val∈Cset n ℓ) : s.val≠0:=by
    have hi:=Finset.mem_Ioc.mp hs
    omega
  unfold diagonalIntegral
  by_cases hPQ : P.1=Q.1
  · have hB : ¬(P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ):=by
      rintro ⟨hC,hQ,hlast⟩
      apply hCne P.1 hC
      rw [hPQ]
      exact hQ
    have hC : ¬(Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ):=by
      rintro ⟨hC,hP,hlast⟩
      apply hCne Q.1 hC
      rw [←hPQ]
      exact hP
    have hz : (P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ)↔
        (P.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ):=by
      constructor
      · rintro ⟨hP,hQ,hPlast,hQlast⟩
        exact ⟨hP,hPlast,hQlast⟩
      · rintro ⟨hP,hPlast,hQlast⟩
        exact ⟨hP,(congrArg Fin.val hPQ).symm.trans hP,hPlast,hQlast⟩
    simp only [if_pos hPQ,if_neg hB,if_neg hC,add_zero,propext hz]
  · have hz : ¬(P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ):=by
      rintro ⟨hP,hQ,hPlast,hQlast⟩
      apply hPQ
      exact Fin.ext (hP.trans hQ.symm)
    simp only [if_neg hPQ,if_neg hz,add_zero,zero_add]
    by_cases hB : P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ
    · have hC : ¬(Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ):=by
        intro h
        exact hCne Q.1 h.1 hB.2.1
      simp only [if_pos hB,if_neg hC,add_zero]
    · by_cases hC : Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ
      · simp only [if_neg hB,if_pos hC,zero_add]
      · simp only [if_neg hB,if_neg hC,zero_add]
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

private theorem Cset_ne_zero (n ℓ : ℕ) (s : Fin ℓ) (hs : s.val∈Cset n ℓ) : s.val≠0:=by
  have hi:=Finset.mem_Ioc.mp hs
  omega
private theorem classIntegral_same {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ) (hP : P.1=s) (hQ : Q.1=s) :
    classIntegral R s P Q=R.units s*R.moments (classKey n ℓ s) (P.2.val+Q.2.val) := by
  have hA : P.1=Q.1∧s=P.1:=⟨hP.trans hQ.symm,hP.symm⟩
  have hB : ¬((P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ)∧s=P.1):=by
    rintro ⟨⟨hC,hQ0,hlast⟩,h⟩
    have hCs : s.val∈Cset n ℓ:=by simpa only [hP] using hC
    exact Cset_ne_zero n ℓ s hCs ((congrArg Fin.val hQ).symm.trans hQ0)
  have hC : ¬((Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ)∧s=Q.1):=by
    rintro ⟨⟨hC,hP0,hlast⟩,h⟩
    have hCs : s.val∈Cset n ℓ:=by simpa only [hQ] using hC
    exact Cset_ne_zero n ℓ s hCs ((congrArg Fin.val hP).symm.trans hP0)
  have hD : ¬((P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ)∧s.val∈Cset n ℓ):=by
    intro h
    exact Cset_ne_zero n ℓ s h.2 ((congrArg Fin.val hP).symm.trans h.1.1)
  simp only [classIntegral,if_pos hA,if_neg hB,if_neg hC,if_neg hD,add_zero]
private theorem classIntegral_mixed_left {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (hs : s.val∈Cset n ℓ) (hP : P.1=s) (hQ : Q.1.val=0) (hlast : Q.2.val+1=m0 n ℓ) :
    classIntegral R s P Q=-(R.units s*(s.val:PadicInt ℓ).inv)*R.moments (keyC n ℓ) (P.2.val+mC n ℓ) := by
  have hP0 : P.1.val≠0:=by simpa only [hP] using Cset_ne_zero n ℓ s hs
  have hQnot : Q.1.val∉Cset n ℓ:=fun h=>Cset_ne_zero n ℓ Q.1 h hQ
  have hA : ¬(P.1=Q.1∧s=P.1):=by rintro ⟨he,h⟩;exact hP0 ((congrArg Fin.val he).trans hQ)
  have hB : (P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ)∧s=P.1:=
    ⟨⟨by simpa only [hP] using hs,hQ,hlast⟩,hP.symm⟩
  simp only [classIntegral,if_neg hA,if_pos hB,hQnot,hP0,false_and,ite_false,zero_add,add_zero]
private theorem classIntegral_mixed_right {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (hs : s.val∈Cset n ℓ) (hP : P.1.val=0) (hlast : P.2.val+1=m0 n ℓ) (hQ : Q.1=s) :
    classIntegral R s P Q=-(R.units s*(s.val:PadicInt ℓ).inv)*R.moments (keyC n ℓ) (Q.2.val+mC n ℓ) := by
  have hQ0 : Q.1.val≠0:=by simpa only [hQ] using Cset_ne_zero n ℓ s hs
  have hPnot : P.1.val∉Cset n ℓ:=fun h=>Cset_ne_zero n ℓ P.1 h hP
  have hA : ¬(P.1=Q.1∧s=P.1):=by rintro ⟨he,h⟩;exact hQ0 ((congrArg Fin.val he).symm.trans hP)
  have hC : (Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ)∧s=Q.1:=
    ⟨⟨by simpa only [hQ] using hs,hP,hlast⟩,hQ.symm⟩
  simp only [classIntegral,if_neg hA,if_pos hC,hPnot,hQ0,false_and,and_false,ite_false,zero_add,add_zero]
private theorem classIntegral_corner {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (hs : s.val∈Cset n ℓ) (hP : P.1.val=0) (hQ : Q.1.val=0)
    (hPlast : P.2.val+1=m0 n ℓ) (hQlast : Q.2.val+1=m0 n ℓ) :
    classIntegral R s P Q=R.units s*(s.val:PadicInt ℓ).inv^2*R.moments (keyC n ℓ) (2*mC n ℓ) := by
  have hsP : s≠P.1:=by intro he;exact Cset_ne_zero n ℓ s hs ((congrArg Fin.val he).trans hP)
  have hPnot : P.1.val∉Cset n ℓ:=fun h=>Cset_ne_zero n ℓ P.1 h hP
  have hQnot : Q.1.val∉Cset n ℓ:=fun h=>Cset_ne_zero n ℓ Q.1 h hQ
  have h0not : 0∉Cset n ℓ:=by simp [Cset]
  simp only [classIntegral,hsP,hPnot,hQnot,h0not,hP,hQ,hPlast,hQlast,hs,false_and,and_false,true_and,ite_false,ite_true,zero_add]

private theorem units_moment_coe {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (A : TypeKey)
    (ha : A.a≤A.c) (hc : A.c<ℓ) (e : ℕ) :
    ((R.units s*R.moments A e:PadicInt ℓ):Padic ℓ)=
      (uQ z n ℓ s:Padic ℓ)*(L A z (X^e):Padic ℓ) := by
  rw [PadicInt.coe_mul,R.units_cast,R.moments_cast A ha hc e]
private theorem units_inv_moment_coe {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (hs : s.val≠0) (A : TypeKey)
    (ha : A.a≤A.c) (hc : A.c<ℓ) (e : ℕ) :
    ((-(R.units s*(s.val:PadicInt ℓ).inv)*R.moments A e:PadicInt ℓ):Padic ℓ)=
      (uQ z n ℓ s:Padic ℓ)/(-(s.val:Padic ℓ))*(L A z (X^e):Padic ℓ) := by
  rw [PadicInt.coe_mul,PadicInt.coe_neg,PadicInt.coe_mul,R.units_cast,
    coe_inv_of_unit ℓ _ (nat_unit_norm ℓ s hs),PadicInt.coe_natCast,R.moments_cast A ha hc e]
  simp only [div_eq_mul_inv,inv_neg,neg_mul,mul_neg]
private theorem units_inv_sq_moment_coe {z : ℚ} {n ℓ : ℕ} [Fact ℓ.Prime]
    (R : ReductionData z n ℓ) (s : Fin ℓ) (hs : s.val≠0) (A : TypeKey)
    (ha : A.a≤A.c) (hc : A.c<ℓ) (e : ℕ) :
    ((R.units s*(s.val:PadicInt ℓ).inv^2*R.moments A e:PadicInt ℓ):Padic ℓ)=
      (uQ z n ℓ s:Padic ℓ)/(s.val:Padic ℓ)^2*(L A z (X^e):Padic ℓ) := by
  rw [PadicInt.coe_mul,PadicInt.coe_mul,R.units_cast,PadicInt.coe_pow,
    coe_inv_of_unit ℓ _ (nat_unit_norm ℓ s hs),PadicInt.coe_natCast,R.moments_cast A ha hc e]
  simp only [div_eq_mul_inv,inv_pow]

private theorem normalized_class_congruence (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (R : ReductionData z n ℓ) (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1))
    (s : Fin ℓ) (P Q : Ix n ℓ) (hpar : nu n ℓ P.1%2=nu n ℓ Q.1%2) :
    Vge ℓ ((ℓ:Padic ℓ)^(-entryExponent n ℓ P Q)*localClass z ℓ s ξ (pairRF n ℓ P Q)-
      ((classIntegral R s P Q:PadicInt ℓ):Padic ℓ)) 1 := by
  obtain ⟨Ψ,hΨ,hf,hs,he,hv,hx,hSame,hTied⟩:=local_expansion z n ℓ hz h1 hR s P Q ξ hξ
  have hb:=entryExponent_bounds n ℓ hR s P Q
  have hm0:=class_zero_count n ℓ hR
  have hnormalize (eN : ℕ) (u a : Padic ℓ)
      (hD : d n ℓ s P+d n ℓ s Q=eN)
      (hdom : nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q=entryExponent n ℓ P Q)
      (hc : ((classIntegral R s P Q:PadicInt ℓ):Padic ℓ)=u*a)
      (hl : Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)-u*(ℓ:Padic ℓ)^(nu n ℓ s+(eN:ℤ))*a)
        (nu n ℓ s+(eN:ℤ)+1)) :
      Vge ℓ ((ℓ:Padic ℓ)^(-entryExponent n ℓ P Q)*localClass z ℓ s ξ (pairRF n ℓ P Q)-
        ((classIntegral R s P Q:PadicInt ℓ):Padic ℓ)) 1:=by
    rw [hc]
    apply normalize_local_leading ℓ _ u a _ _ _ hl
    have hh:=congrArg (fun m : ℕ=>(m:ℤ)) hD
    push_cast at hh
    omega
  by_cases hA : P.1=Q.1∧s=P.1
  · have hP : P.1=s:=hA.2.symm
    have hQ : Q.1=s:=hA.1.symm.trans hP
    have hdom:= (hb.2.2 hpar).2 (Or.inl ⟨hP.symm,hQ.symm⟩)
    have hvalid:=class_key_valid n ℓ hR s
    refine hnormalize (P.2.val+Q.2.val) (uQ z n ℓ s:Padic ℓ)
      (L (classKey n ℓ s) z (X^(P.2.val+Q.2.val)):Padic ℓ)
      (by simp only [d,if_pos hP.symm,if_pos hQ.symm]) hdom ?_ ?_
    · rw [classIntegral_same R s P Q hP hQ]
      exact units_moment_coe R s _ hvalid.1 hvalid.2 _
    · simpa only [Nat.cast_add,add_assoc] using hSame P Q hP hQ
  · by_cases hB : (P.1.val∈Cset n ℓ∧Q.1.val=0∧Q.2.val+1=m0 n ℓ)∧s=P.1
    · have hP : P.1=s:=hB.2.symm
      have hC : s.val∈Cset n ℓ:=by simpa only [hP] using hB.1.1
      have hQ0:=hB.1.2.1
      have hlast:=hB.1.2.2
      have hPQ : P.1≠Q.1:=by intro hh;exact Cset_ne_zero n ℓ P.1 hB.1.1 ((congrArg Fin.val hh).trans hQ0)
      have hsQ : s≠Q.1:=by intro hh;exact Cset_ne_zero n ℓ s hC ((congrArg Fin.val hh).trans hQ0)
      have hdom:=(hb.2.2 hpar).2 (Or.inr (Or.inl
        ⟨hP.symm,hPQ,(class_C_iff n ℓ s).2 hC,hQ0,hlast.trans hm0.symm⟩))
      have hvalid:=class_C_key_valid n ℓ hR s hC
      have hmC:=(class_C_key n ℓ hR s hC).2.1
      refine hnormalize (P.2.val+mC n ℓ) ((uQ z n ℓ s:Padic ℓ)/(-(s.val:Padic ℓ)))
        (L (keyC n ℓ) z (X^(P.2.val+mC n ℓ)):Padic ℓ)
        (by simp only [d,if_pos hP.symm,if_neg hsQ,hmC]) hdom ?_ ?_
      · rw [classIntegral_mixed_left R s P Q hC hP hQ0 hlast]
        exact units_inv_moment_coe R s (Cset_ne_zero n ℓ s hC) _ hvalid.1 hvalid.2 _
      · simpa only [Nat.cast_add,add_assoc] using (hTied hC).1 P Q hP hQ0 hlast
    · by_cases hC : (Q.1.val∈Cset n ℓ∧P.1.val=0∧P.2.val+1=m0 n ℓ)∧s=Q.1
      · have hQ : Q.1=s:=hC.2.symm
        have hsC : s.val∈Cset n ℓ:=by simpa only [hQ] using hC.1.1
        have hP0:=hC.1.2.1
        have hlast:=hC.1.2.2
        have hPQ : P.1≠Q.1:=by intro hh;exact Cset_ne_zero n ℓ Q.1 hC.1.1 ((congrArg Fin.val hh).symm.trans hP0)
        have hsP : s≠P.1:=by intro hh;exact Cset_ne_zero n ℓ s hsC ((congrArg Fin.val hh).trans hP0)
        have hdom:=(hb.2.2 hpar).2 (Or.inr (Or.inr (Or.inl
          ⟨hQ.symm,hPQ,(class_C_iff n ℓ s).2 hsC,hP0,hlast.trans hm0.symm⟩)))
        have hvalid:=class_C_key_valid n ℓ hR s hsC
        have hmC:=(class_C_key n ℓ hR s hsC).2.1
        refine hnormalize (Q.2.val+mC n ℓ) ((uQ z n ℓ s:Padic ℓ)/(-(s.val:Padic ℓ)))
          (L (keyC n ℓ) z (X^(Q.2.val+mC n ℓ)):Padic ℓ)
          (by simp only [d,if_neg hsP,if_pos hQ.symm,hmC];omega) hdom ?_ ?_
        · rw [classIntegral_mixed_right R s P Q hsC hP0 hlast hQ]
          exact units_inv_moment_coe R s (Cset_ne_zero n ℓ s hsC) _ hvalid.1 hvalid.2 _
        · have hh:=(hTied hsC).1 Q P hQ hP0 hlast
          rw [←pairRF_comm n ℓ P Q] at hh
          simpa only [Nat.cast_add,add_assoc] using hh
      · by_cases hD : (P.1.val=0∧Q.1.val=0∧P.2.val+1=m0 n ℓ∧Q.2.val+1=m0 n ℓ)∧s.val∈Cset n ℓ
        · have hsC:=hD.2
          have hP0:=hD.1.1
          have hQ0:=hD.1.2.1
          have hPlast:=hD.1.2.2.1
          have hQlast:=hD.1.2.2.2
          have hsP : s≠P.1:=by intro hh;exact Cset_ne_zero n ℓ s hsC ((congrArg Fin.val hh).trans hP0)
          have hsQ : s≠Q.1:=by intro hh;exact Cset_ne_zero n ℓ s hsC ((congrArg Fin.val hh).trans hQ0)
          have hdom:=(hb.2.2 hpar).2 (Or.inr (Or.inr (Or.inr
            ⟨(class_C_iff n ℓ s).2 hsC,hP0,hQ0,hPlast.trans hm0.symm,hQlast.trans hm0.symm⟩)))
          have hvalid:=class_C_key_valid n ℓ hR s hsC
          have hmC:=(class_C_key n ℓ hR s hsC).2.1
          refine hnormalize (2*mC n ℓ) ((uQ z n ℓ s:Padic ℓ)/(s.val:Padic ℓ)^2)
            (L (keyC n ℓ) z (X^(2*mC n ℓ)):Padic ℓ)
            (by simp only [d,if_neg hsP,if_neg hsQ,hmC];omega) hdom ?_ ?_
          · rw [classIntegral_corner R s P Q hsC hP0 hQ0 hPlast hQlast]
            exact units_inv_sq_moment_coe R s (Cset_ne_zero n ℓ s hsC) _ hvalid.1 hvalid.2 _
          · simpa only [Nat.cast_mul,Nat.cast_ofNat,add_assoc] using (hTied hsC).2 P Q hP0 hQ0 hPlast hQlast
        · have hneq : nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q≠entryExponent n ℓ P Q:=by
            intro hh
            rcases (hb.2.2 hpar).1 hh with ⟨hP,hQ⟩|hEx
            · exact hA ⟨hP.symm.trans hQ,hP⟩
            · rcases hEx with ⟨hP,hPQ,hCs,hQ0,hlast⟩|⟨hQ,hPQ,hCs,hP0,hlast⟩|⟨hCs,hP0,hQ0,hPlast,hQlast⟩
              · have hSC:=(class_C_iff n ℓ s).1 hCs
                have hPC : P.1.val∈Cset n ℓ:=by simpa only [hP] using hSC
                exact hB ⟨⟨hPC,hQ0,hlast.trans hm0⟩,hP⟩
              · have hSC:=(class_C_iff n ℓ s).1 hCs
                have hQC : Q.1.val∈Cset n ℓ:=by simpa only [hQ] using hSC
                exact hC ⟨⟨hQC,hP0,hlast.trans hm0⟩,hQ⟩
              · exact hD ⟨⟨hP0,hQ0,hPlast.trans hm0,hQlast.trans hm0⟩,(class_C_iff n ℓ s).1 hCs⟩
          have hzero : classIntegral R s P Q=0:=by
            simp only [classIntegral,if_neg hA,if_neg hB,if_neg hC,if_neg hD,zero_add]
          rw [hzero,PadicInt.coe_zero,sub_zero]
          have hh:=Vge_mul_levels ℓ _ _ (-entryExponent n ℓ P Q)
            (nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q) (Vge_prime_power ℓ _) hv
          exact Vge_mono ℓ _ _ 1 (by omega) hh

private theorem normalized_gram_diagonal (z x : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (hx : Vge ℓ (x:Padic ℓ) (-1)) (R : ReductionData z n ℓ)
    (P Q : Ix n ℓ) (hpar : nu n ℓ P.1%2=nu n ℓ Q.1%2) :
    Vge ℓ (((normalizedGram z n ℓ x P Q:ℚ):Padic ℓ)-
      ((diagonalIntegral R P Q:PadicInt ℓ):Padic ℓ)) 1 := by
  classical
  obtain ⟨L,hL⟩:=(regularization_constant z ℓ hz h1).2.2
  let ξ:=(x:Padic ℓ)-(L:Padic ℓ)
  have hξ : Vge ℓ ξ (-1):=coordinate_sub_integral_bound ℓ _ hx L
  have hsum : ((normalizedGram z n ℓ x P Q:ℚ):Padic ℓ)=
      ∑s : Fin ℓ,(ℓ:Padic ℓ)^(-entryExponent n ℓ P Q)*localClass z ℓ s ξ (pairRF n ℓ P Q):=by
    simp only [normalizedGram,Rat.cast_mul,Rat.cast_zpow,Rat.cast_natCast]
    rw [gram_local_distribution z x n ℓ hz h1 L hL P Q,Finset.mul_sum]
  have hdiag : ((diagonalIntegral R P Q:PadicInt ℓ):Padic ℓ)=
      ∑s : Fin ℓ,((classIntegral R s P Q:PadicInt ℓ):Padic ℓ):=by
    rw [←classIntegral_sum]
    simpa only [PadicInt.Coe.ringHom_apply] using
      map_sum (PadicInt.Coe.ringHom : PadicInt ℓ→+*Padic ℓ) (fun s : Fin ℓ=>classIntegral R s P Q) Finset.univ
  rw [hsum,hdiag,←Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro s hs
  exact normalized_class_congruence z n ℓ hz h1 hR R ξ hξ s P Q hpar
theorem scaled_gram_reduction (z x : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (hx : Vge ℓ (x:Padic ℓ) (-1)) :
  ∃ (R : ReductionData z n ℓ) (upper : Matrix (Ix n ℓ) (Ix n ℓ) (ZMod ℓ))
    (Ξ : ℕ) (ex ey : Ix n ℓ→ℕ)
    (Z : Matrix (Ix n ℓ) (Ix n ℓ) (Basic.LocRing ℓ)),
    (∀ P, (ex P:ℤ)=(P.2:ℤ)+(nu n ℓ P.1-nu n ℓ P.1%2)/2+Ξ ∧
      (ey P:ℤ)=(P.2:ℤ)+(nu n ℓ P.1+nu n ℓ P.1%2)/2+Ξ) ∧
    (∀ P Q, (ℓ:ℚ)^(2*Ξ)*G z n ℓ x P Q=
      (ℓ:ℚ)^(ex P)*(Z P Q:ℚ)*(ℓ:ℚ)^(ey Q)) ∧
    (Arith.Hybrid.redQ ℓ).mapMatrix Z=expectedReduction R upper
 := by
  classical
  obtain ⟨R⟩:=reduction_data_exists z n ℓ hz h1
  obtain ⟨Ξ,ex,ey,Z,hE,hfactor,hZ,hBA⟩:=scaled_gram_integral_lift z x n ℓ hz h1 hR hx
  let upper:=(Arith.Hybrid.redQ ℓ).mapMatrix Z
  refine ⟨R,upper,Ξ,ex,ey,Z,hE,hfactor,?_⟩
  ext P Q
  change Arith.Hybrid.redQ ℓ (Z P Q)=expectedReduction R upper P Q
  unfold expectedReduction
  by_cases hpar : nu n ℓ P.1%2=nu n ℓ Q.1%2
  · rw [if_pos hpar]
    have hv : Vge ℓ ((((locToPadicInt ℓ (Z P Q)):PadicInt ℓ):Padic ℓ)-
        ((diagonalIntegral R P Q:PadicInt ℓ):Padic ℓ)) 1:=by
      change Vge ℓ (((Z P Q:ℚ):Padic ℓ)-((diagonalIntegral R P Q:PadicInt ℓ):Padic ℓ)) 1
      rw [hZ]
      exact normalized_gram_diagonal z x n ℓ hz h1 hR hx R P Q hpar
    have hr:=reduce_eq_of_Vge ℓ (locToPadicInt ℓ (Z P Q)) (diagonalIntegral R P Q) hv
    rw [locToPadicInt_red] at hr
    change Arith.Hybrid.redQ ℓ (Z P Q)=reduceInt ℓ (diagonalIntegral R P Q) at hr
    rw [diagonalIntegral_red] at hr
    exact hr
  · rw [if_neg hpar]
    by_cases hP : nu n ℓ P.1%2=0
    · rw [if_pos hP]
      rfl
    · rw [if_neg hP]
      have hQ : nu n ℓ Q.1%2=0:=by omega
      exact hBA P Q hP hQ
#print axioms scaled_gram_reduction
end
end CatalanCore.Li2.NV
