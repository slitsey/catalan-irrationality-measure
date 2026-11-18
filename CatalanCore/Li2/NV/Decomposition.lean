module
public import CatalanCore.Li2.NV.Local
public import Mathlib.Algebra.Polynomial.Sequence
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
private theorem shift_eigen_zero (z : ℚ) (hz : z≠1) (L : ℚ[X]→ₗ[ℚ]ℚ)
    (hL : ∀P,L (P.comp (X-1))=z*L P) : L=0 := by
  have hd : ∀ n,L (descPochhammer ℚ n)=0 := by
    intro n
    induction n with
    | zero=>
      have h:=hL 1
      simp only [one_comp] at h
      have hh : (1-z)*L 1=0:=by linear_combination h
      have he:= (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (Ne.symm hz))
      simpa only [descPochhammer_zero] using he
    | succ n ih=>
      have h:=congrArg L (descPochhammer_succ_comp_X_sub_one ℚ n)
      have hc : (n+(1:ℚ[X]))=C ((n:ℚ)+1):=by simp
      simp only [smul_eq_mul,hc,map_sub,show ∀a P,L (C a*P)=a*L P from
        fun a P=>by simpa only [RingHom.id_apply,Polynomial.smul_eq_C_mul,smul_eq_mul] using L.map_smul a P,hL,ih,mul_zero,sub_zero] at h
      have hh : (1-z)*L (descPochhammer ℚ (n+1))=0:=by linear_combination -h
      exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (Ne.symm hz))
  let seq : Polynomial.Sequence ℚ:={
    elems':=descPochhammer ℚ
    degree_eq':=fun n=>by rw [degree_eq_natDegree (monic_descPochhammer ℚ n).ne_zero,descPochhammer_natDegree]}
  have hu : ∀n,IsUnit (seq n).leadingCoeff:=fun n=>by
    change IsUnit (descPochhammer ℚ n).leadingCoeff
    rw [(monic_descPochhammer ℚ n).leadingCoeff]
    exact isUnit_one
  apply (seq.basis hu).ext
  intro n
  simpa only [Polynomial.Sequence.basis_eq_self,LinearMap.zero_apply] using hd n
private def parameterGLinear (z : ℚ) : ℚ[X]→ₗ[ℚ]ℚ where
  toFun:=Port.Li2.parameterG z
  map_add':=Port.Li2.parameterG_add z
  map_smul' a P:=by
    simpa only [RingHom.id_apply,Polynomial.smul_eq_C_mul,smul_eq_mul] using Port.Li2.parameterG_C_mul z a P
private def dissectG (z : ℚ) (q : ℕ) (P : ℚ[X]) : ℚ:=
  ∑ s∈Finset.range q,z^(-(s:ℤ))*Port.Li2.parameterG (z^q)
    (P.comp (C (q:ℚ)*X-C (s:ℚ)))
private def dissectLinear (z : ℚ) (q : ℕ) : ℚ[X]→ₗ[ℚ]ℚ where
  toFun:=dissectG z q
  map_add' P Q:=by
    simp only [dissectG,add_comp,Port.Li2.parameterG_add,mul_add,Finset.sum_add_distrib]
  map_smul' a P:=by
    simp only [RingHom.id_apply,dissectG,Polynomial.smul_eq_C_mul,smul_eq_mul,mul_comp,C_comp,
      Port.Li2.parameterG_C_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
private theorem parameterG_shift_back (z : ℚ) (hz : z≠1) (P : ℚ[X]) :
    Port.Li2.parameterG z (P.comp (X-1))=z*(P.eval 0+Port.Li2.parameterG z P) := by
  have he : ((X:ℚ[X])-1).comp (X+1)=X:=by simp
  have hc : (P.comp (X-1)).comp (X+1)=P:=by rw [comp_assoc,he,comp_X]
  have hv : (P.comp (X-1)).eval 1=P.eval 0:=by simp
  have hh:=Port.Li2.parameterG_shift_one z hz (P.comp (X-1))
  rw [hc,hv] at hh
  linear_combination -hh
private theorem dissect_shift_back (z : ℚ) (hz : z≠0) (q : ℕ) (hq : 0<q)
    (hw : z^q≠1) (P : ℚ[X]) :
    dissectG z q (P.comp (X-1))=z*(P.eval 0+dissectG z q P) := by
  let f : ℕ→ℚ:=fun s=>z^(-(s:ℤ))*Port.Li2.parameterG (z^q)
    (P.comp (C (q:ℚ)*X-C (s:ℚ)))
  have hs : dissectG z q (P.comp (X-1))=z*(∑ s∈Finset.range q,f (s+1)) := by
    unfold dissectG
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hp : (P.comp (X-1)).comp (C (q:ℚ)*X-C (s:ℚ))=
        P.comp (C (q:ℚ)*X-C ((s+1:ℕ):ℚ)) := by
      rw [comp_assoc]
      congr 1
      simp only [sub_comp,X_comp,one_comp,Nat.cast_add,Nat.cast_one]
      simp only [map_add,map_one]
      ring
    rw [hp]
    dsimp only [f]
    have hzpow : z*z^(-((s+1:ℕ):ℤ))=z^(-(s:ℤ)) := by
      calc
        _=z^((1:ℤ)+ -((s+1:ℕ):ℤ)):=by
          simpa only [zpow_one] using (_root_.zpow_add₀ hz (1:ℤ) (-((s+1:ℕ):ℤ))).symm
        _=z^(-(s:ℤ)):=by congr 1;push_cast;ring
    rw [←mul_assoc,hzpow]
  have hb : f q=P.eval 0+f 0 := by
    have hp : P.comp (C (q:ℚ)*X-C (q:ℚ))=
        (P.comp (C (q:ℚ)*X)).comp (X-1) := by
      rw [comp_assoc]
      congr 1
      simp only [mul_comp,C_comp,X_comp]
      ring
    dsimp only [f]
    rw [hp,parameterG_shift_back (z^q) hw]
    have hv : (P.comp (C (q:ℚ)*X)).eval 0=P.eval 0:=by simp
    rw [hv]
    have hc : z^(-(q:ℤ))*z^q=1:=by
      rw [←zpow_natCast z q,←_root_.zpow_add₀ hz,neg_add_cancel,zpow_zero]
    rw [←mul_assoc,hc,one_mul]
    simp only [Nat.cast_zero,Int.natCast_zero,neg_zero,zpow_zero,one_mul,
      C_0,sub_zero]
  have h0:=Finset.sum_range_succ f q
  have h1:=Finset.sum_range_succ' f q
  have he : (∑ s∈Finset.range q,f (s+1))=P.eval 0+∑ s∈Finset.range q,f s:=by
    linear_combination h0-h1+hb
  rw [hs,he]
  rfl

private theorem dissectG_eq_parameterG (z : ℚ) (hz : z≠0) (h1 : z≠1) (q : ℕ)
    (hq : 0<q) (hw : z^q≠1) (P : ℚ[X]) :
    dissectG z q P=Port.Li2.parameterG z P := by
  let L:=dissectLinear z q-parameterGLinear z
  have hL : ∀Q : ℚ[X],L (Q.comp (X-1))=z*L Q:=by
    intro Q
    change dissectG z q (Q.comp (X-1))-Port.Li2.parameterG z (Q.comp (X-1))=
      z*(dissectG z q Q-Port.Li2.parameterG z Q)
    rw [dissect_shift_back z hz q hq hw,parameterG_shift_back z h1]
    ring
  have he:=DFunLike.congr_fun (shift_eigen_zero z h1 L hL) P
  change dissectG z q P-Port.Li2.parameterG z P=0 at he
  exact sub_eq_zero.mp he
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
theorem li_distribution (z : ℚ) (hz : z≠0) (h1 : z≠1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hpow : z^ℓ≠1) (j : ℕ) :
    NVMod.liNeg j z=∑ s : Fin ℓ,z^(-(s:ℤ))*
      ∑ i∈Finset.range (j+1),(Nat.choose j i:ℚ)*(-(s:ℚ))^(j-i)*
        (ℓ:ℚ)^i*NVMod.liNeg i (z^ℓ) := by
  rw [liNeg_eq_parameterMoment z h1]
  simp_rw [liNeg_eq_parameterMoment (z^ℓ) hpow]
  have he:=dissectG_eq_parameterG z hz h1 ℓ (Fact.out : ℓ.Prime).pos hpow (X^j)
  have hg : Port.Li2.parameterG z (X^j)=Port.Li2.parameterMoment z j:=by
    simpa using Port.Li2.parameterG_C_mul_X_pow z 1 j
  rw [hg] at he
  unfold dissectG at he
  simp only [pow_comp,X_comp] at he
  simp_rw [parameterG_affine_power] at he
  rw [←Fin.sum_univ_eq_sum_range] at he
  exact he.symm

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
private theorem tau_dissection (z : ℚ) (ℓ j : ℕ) [Fact ℓ.Prime] :
    tauK z j=(∑ b∈(Finset.Icc 1 j).filter (fun b=>¬ℓ∣b),z^b/(b:ℚ)^2)+
      tauK (z^ℓ) (j/ℓ)/(ℓ:ℚ)^2 := by
  classical
  have hp : 0<ℓ:=(Fact.out : ℓ.Prime).pos
  let f : ℕ→ℚ:=fun b=>z^b/(b:ℚ)^2
  have he : (∑ k∈Finset.Icc 1 (j/ℓ),f (ℓ*k))=
      ∑ b∈(Finset.Icc 1 j).filter (fun b=>ℓ∣b),f b := by
    apply Finset.sum_bij (fun k hk=>ℓ*k)
    · intro k hk
      have hi:=Finset.mem_Icc.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith,?_⟩,dvd_mul_right _ _⟩
      have hb:=Nat.mul_div_le j ℓ
      exact le_trans (Nat.mul_le_mul_left ℓ hi.2) (by simpa only [Nat.mul_comm] using hb)
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp hab
    · intro b hb
      obtain ⟨hI,hd⟩:=Finset.mem_filter.mp hb
      obtain ⟨k,rfl⟩:=hd
      refine ⟨k,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
      · have hi:=(Finset.mem_Icc.mp hI).1
        nlinarith
      · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hI).2)
    · intro k hk
      rfl
  have hs : (∑ k∈Finset.Icc 1 (j/ℓ),f (ℓ*k))=tauK (z^ℓ) (j/ℓ)/(ℓ:ℚ)^2 := by
    unfold tauK
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [Nat.cast_mul,mul_pow,pow_mul]
    ring
  change (∑ b∈Finset.Icc 1 j,f b)=(∑ b∈(Finset.Icc 1 j).filter (fun b=>¬ℓ∣b),f b)+tauK (z^ℓ) (j/ℓ)/(ℓ:ℚ)^2
  rw [←hs,he]
  simpa only [not_not] using (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 j) (fun b=>¬ℓ∣b) f).symm

theorem decompose_simple_pole (z x : ℚ) (ℓ j : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (hj : 0<j)
    (L : PadicInt ℓ) (hL : ∀ k≥1,T z ℓ k=(L:Padic ℓ)) :
    (li2Lambda z x ((rfX+rfPoly (C (j:ℚ)))⁻¹):Padic ℓ)=
      ∑ s : Fin ℓ,localClass z ℓ s ((x:Padic ℓ)-L)
        ((rfX+rfPoly (C (j:ℚ)))⁻¹) := by
  classical
  have hp : 0<ℓ:=(Fact.out : ℓ.Prime).pos
  have hz0 : (z:Padic ℓ)≠0:=by
    intro he
    have hh:=hz
    simp only [Unit,he,norm_zero] at hh
    exact zero_ne_one hh
  have hℓ : (ℓ:Padic ℓ)≠0:=by exact_mod_cast (Nat.ne_of_gt hp)
  let r : Fin ℓ:=⟨j%ℓ,Nat.mod_lt j hp⟩
  let A : Padic ℓ:=(z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
    ((ℓ:Padic ℓ)^2*((x:Padic ℓ)-L)-(tauK (z^ℓ) (j/ℓ):ℚ))
  let B : Fin ℓ→Padic ℓ:=fun s=>(z:Padic ℓ)^(-(s:ℤ))*E z ℓ ((j:ℤ)-s.val)
  let R : Padic ℓ:=∑ s : Fin ℓ,if j%ℓ≠s.val then B s else 0
  let tail : Padic ℓ:=∑ b∈(Finset.Icc 1 j).filter (fun b=>¬ℓ∣b),(z:Padic ℓ)^b/(b:Padic ℓ)^2
  have hir (s : Fin ℓ) : (j%ℓ=s.val) ↔ s=r:=by
    change r.val=s.val ↔ s=r
    rw [Fin.ext_iff]
    exact eq_comm
  have hsplit : (∑ s : Fin ℓ,if j%ℓ=s.val then A else B s)=A+R := by
    calc
      _=(∑ s : Fin ℓ,if s=r then A else 0)+(∑ s : Fin ℓ,if j%ℓ≠s.val then B s else 0):=by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases he : j%ℓ=s.val
        · simp [he,(hir s).mp he]
        · have hne : s≠r:=fun h=>he ((hir s).mpr h)
          simp [he,hne]
      _=A+R:=by simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,R]
  have hscaled : (z:Padic ℓ)^(-(j:ℤ))*tail+R=
      (z:Padic ℓ)^(-(j:ℤ))*(L:Padic ℓ) := by
    have ht:=congrArg (fun v : Padic ℓ=>(z:Padic ℓ)^(-(j:ℤ))*v) (hL j (by omega))
    unfold T at ht
    rw [mul_add,Finset.mul_sum,Finset.mul_sum] at ht
    have hs : (∑ s : Fin ℓ,(z:Padic ℓ)^(-(j:ℤ))*
        (if j%ℓ≠s.val then (z:Padic ℓ)^((j:ℤ)-s.val)*E z ℓ ((j:ℤ)-s.val) else 0))=R := by
      apply Finset.sum_congr rfl
      intro s hs
      dsimp only [B]
      by_cases he : j%ℓ≠s.val
      · simp only [if_pos he]
        rw [←mul_assoc,←_root_.zpow_add₀ hz0]
        congr 2
        ring
      · simp only [if_neg he,mul_zero]
    rw [hs] at ht
    simpa only [tail,Finset.mul_sum] using! ht
  have hR : R=(z:Padic ℓ)^(-(j:ℤ))*(L:Padic ℓ)-(z:Padic ℓ)^(-(j:ℤ))*tail:=by
    linear_combination hscaled
  have hτ : ((tauK z j:ℚ):Padic ℓ)=tail+
      ((tauK (z^ℓ) (j/ℓ):ℚ):Padic ℓ)/(ℓ:Padic ℓ)^2:=by
    have hh:=congrArg (fun q : ℚ=>(q:Padic ℓ)) (tau_dissection z ℓ j)
    simpa only [Rat.cast_add,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,tail] using hh
  rw [(simple_pole_values z x ℓ j ((x:Padic ℓ)-L) r).1]
  simp only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_zpow,Rat.cast_sub]
  have hc : (∑ s : Fin ℓ,localClass z ℓ s ((x:Padic ℓ)-L)
      ((rfX+rfPoly (C (j:ℚ)))⁻¹))=(j:Padic ℓ)*(A+R) := by
    simp_rw [fun s=>(simple_pole_values z x ℓ j ((x:Padic ℓ)-L) s).2]
    rw [←Finset.mul_sum]
    exact congrArg ((j:Padic ℓ)*·) hsplit
  rw [hc,hR,hτ]
  dsimp only [A]
  field_simp
  <;> ring

#print axioms li_distribution
#print axioms decompose_simple_pole
end
end CatalanCore.Li2.NV


