module
public import CatalanCore.Li2.NV.Family
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimeRestrictedShift
public import CatalanCore.Li2.Port.Unified.Modular.Base.PadicReciprocalSeries
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset Filter
open scoped BigOperators Topology
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
abbrev Germ (ℓ : ℕ) [Fact ℓ.Prime] := ℕ→PadicInt ℓ
noncomputable def S (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) : Padic ℓ :=
  ∑' j : ℕ, (H j:Padic ℓ)*(ℓ:Padic ℓ)^j*(liNeg j (z^ℓ):ℚ)
noncomputable def shiftGerm (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) (i : ℕ) : PadicInt ℓ :=
  ∑' j : ℕ, H (i+j)*(Nat.choose (i+j) i:PadicInt ℓ)*(ℓ:PadicInt ℓ)^j
noncomputable def germEval (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) (u : Padic ℓ) : Padic ℓ :=
  ∑' j : ℕ, (H j:Padic ℓ)*(ℓ*u)^j
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
private theorem li_shift (z : ℚ) (hz : z≠1) (j : ℕ) :
    z*(∑ i∈Finset.range (j+1),(Nat.choose j i:ℚ)*liNeg i z)=liNeg j z-z := by
  simp_rw [liNeg_eq_parameterMoment z hz]
  have hh:=Port.Li2.parameterMoment_full_recurrence z hz j
  linear_combination -hh
private theorem li_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (j : ℕ) :
    Intg ℓ ((liNeg j (z^ℓ):ℚ):Padic ℓ) := by
  have hh:=parameter_hypotheses z ℓ hz h1
  rw [liNeg_eq_parameterMoment (z^ℓ) hh.2.2.2]
  exact Port.Li2.padic_norm_le_one_of_VG (Port.Li2.parameterMoment_VG ℓ (z^ℓ) hh.2.2.1 j)
private def germScaled (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) : PowerSeries (PadicInt ℓ):=
  PowerSeries.mk (fun j=>H j*(ℓ:PadicInt ℓ)^j)
private theorem germScaled_restricted (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) :
    PowerSeries.IsRestricted 1 (germScaled ℓ H) := by
  rw [PowerSeries.isRestricted_iff']
  simp only [germScaled,PowerSeries.coeff_mk,one_pow,mul_one,norm_mul,norm_pow]
  apply squeeze_zero (fun j=>mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    (fun j=>?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (ℓ:PadicInt ℓ))
      Port.Li2.padicInt_prime_norm_lt_one)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (PadicInt.norm_le_one (H j))
    (pow_nonneg (norm_nonneg (ℓ:PadicInt ℓ)) j)
private theorem S_summable (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (H : Germ ℓ) :
    Summable (fun j : ℕ=>(H j:Padic ℓ)*(ℓ:Padic ℓ)^j*(liNeg j (z^ℓ):ℚ)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop,tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun j=>norm_nonneg _) (fun j=>?_) 
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (ℓ:Padic ℓ))
      (by simpa only [←PadicInt.coe_natCast,PadicInt.norm_def] using
        (Port.Li2.padicInt_prime_norm_lt_one (p:=ℓ))))
  rw [norm_mul,norm_mul,norm_pow]
  calc
    ‖(H j:Padic ℓ)‖*‖(ℓ:Padic ℓ)‖^j*‖((liNeg j (z^ℓ):ℚ):Padic ℓ)‖
      ≤1*‖(ℓ:Padic ℓ)‖^j*1:=mul_le_mul
        (mul_le_mul_of_nonneg_right (PadicInt.norm_le_one (H j)) (pow_nonneg (norm_nonneg _) j))
        (li_integral z ℓ hz h1 j) (norm_nonneg _) (by positivity)
    _=‖(ℓ:Padic ℓ)‖^j:=by ring
private theorem S_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (H : Germ ℓ) :
    Intg ℓ (S z ℓ H) := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro j
  rw [norm_mul,norm_mul,norm_pow]
  have hp : ‖(ℓ:Padic ℓ)‖≤1:=by
    simpa only [←PadicInt.coe_natCast,PadicInt.norm_def] using PadicInt.norm_le_one (ℓ:PadicInt ℓ)
  simpa using mul_le_mul
    (mul_le_one₀ (PadicInt.norm_le_one (H j)) (pow_nonneg (norm_nonneg (ℓ:Padic ℓ)) j)
      (pow_le_one₀ (norm_nonneg _) hp))
    (li_integral z ℓ hz h1 j) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
private theorem S_eq_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (H : Germ ℓ) :
    S z ℓ H=(Port.Li2.restrictedMoment
      (Port.Li2.integralParameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.1)
      (germScaled ℓ H):Padic ℓ) := by
  have hh:=(Port.Li2.restrictedMoment_summable
    (Port.Li2.integralParameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.1)
    (germScaled ℓ H) (germScaled_restricted ℓ H)).map_tsum
    PadicInt.Coe.ringHom PadicInt.isOpenEmbedding_coe.continuous
  simp_rw [S,liNeg_eq_parameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.2]
  simpa only [S,Port.Li2.restrictedMoment,germScaled,PowerSeries.coeff_mk,
    PadicInt.Coe.ringHom_apply,map_mul,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast,
    Port.Li2.integralParameterMoment,Port.Li2.integralRational] using! hh.symm

private theorem shiftGerm_summable (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) (i : ℕ) :
    Summable (fun j : ℕ=>H (i+j)*(Nat.choose (i+j) i:PadicInt ℓ)*(ℓ:PadicInt ℓ)^j) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop,tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun j=>norm_nonneg _) (fun j=>?_) 
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (ℓ:PadicInt ℓ))
      Port.Li2.padicInt_prime_norm_lt_one)
  rw [norm_mul,norm_mul,norm_pow]
  exact le_trans (mul_le_mul_of_nonneg_right
    (mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) (PadicInt.norm_le_one _))
    (pow_nonneg (norm_nonneg _) j)) (by rw [one_mul])
private theorem germScaled_shift (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) :
    germScaled ℓ (shiftGerm ℓ H)=Port.Li2.restrictedTranslate 1 (germScaled ℓ H) := by
  apply PowerSeries.ext
  intro i
  simp only [germScaled,Port.Li2.restrictedTranslate,PowerSeries.coeff_mk,shiftGerm,one_pow,mul_one]
  rw [←(shiftGerm_summable ℓ H i).tsum_mul_right]
  apply tsum_congr
  intro j
  rw [pow_add]
  ring
private theorem S_add (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (H J : Germ ℓ) :
    S z ℓ (H+J)=S z ℓ H+S z ℓ J := by
  simp only [S,Pi.add_apply,PadicInt.coe_add,add_mul]
  exact (S_summable z ℓ hz h1 H).tsum_add (S_summable z ℓ hz h1 J)
private theorem S_smul (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (a : PadicInt ℓ) (H : Germ ℓ) :
    S z ℓ (a • H)=(a:Padic ℓ)*S z ℓ H := by
  simp only [S,Pi.smul_apply,smul_eq_mul,PadicInt.coe_mul,mul_assoc]
  simpa only [mul_assoc] using (S_summable z ℓ hz h1 H).tsum_mul_left (a:Padic ℓ)
private theorem germEval_eq_integral (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) :
    germEval ℓ H 1=(Port.Li2.restrictedEval 1 (germScaled ℓ H):Padic ℓ) := by
  have hh:=(Port.Li2.restrictedMoment_summable (fun j=>(1:PadicInt ℓ)^j)
    (germScaled ℓ H) (germScaled_restricted ℓ H)).map_tsum
    PadicInt.Coe.ringHom PadicInt.isOpenEmbedding_coe.continuous
  simpa only [germEval,Port.Li2.restrictedEval,Port.Li2.restrictedMoment,
    germScaled,PowerSeries.coeff_mk,PadicInt.Coe.ringHom_apply,map_mul,PadicInt.coe_mul,PadicInt.coe_pow,
    PadicInt.coe_natCast,one_pow,mul_one] using! hh.symm
private theorem S_shift (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (H : Germ ℓ) :
    S z ℓ (shiftGerm ℓ H)=(z:Padic ℓ)^(-(ℓ:ℤ))*
      (S z ℓ H-(z:Padic ℓ)^ℓ*germEval ℓ H 1) := by
  have hh:=parameter_hypotheses z ℓ hz h1
  have hs:=Port.Li2.padicParameterG_shift (z^ℓ) hh.2.1 hh.2.2.1 hh.2.2.2
    (pow_ne_zero ℓ hh.1) (germScaled ℓ H) (germScaled_restricted ℓ H) 1
  rw [S_eq_integral z ℓ hz h1 (shiftGerm ℓ H),S_eq_integral z ℓ hz h1 H,
    germScaled_shift,germEval_eq_integral]
  simp only [Nat.cast_one,Finset.sum_range_one,Nat.zero_add,pow_one,zero_add,Rat.cast_pow,Port.Li2.padicParameterG,PadicInt.coe_zero] at hs
  rw [hs,_root_.zpow_neg,zpow_natCast]
  ring

private theorem liNeg_ratCast (j : ℕ) (w : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    ((liNeg j w:ℚ):Padic ℓ)=liNeg j (w:Padic ℓ) := by
  unfold liNeg
  split_ifs <;> push_cast <;> rfl
theorem li_shift_and_germ (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) :
  (∀ j,z*(∑ i∈Finset.range (j+1),(Nat.choose j i:ℚ)*liNeg i z)=liNeg j z-z) ∧
  (∀ j,Intg ℓ (liNeg j (z^ℓ):Padic ℓ)) ∧
  (∀ H : Germ ℓ,Summable (fun j=>(H j:Padic ℓ)*(ℓ:Padic ℓ)^j*(liNeg j (z^ℓ):ℚ))) ∧
  (∀ H : Germ ℓ,Intg ℓ (S z ℓ H) ∧
    S z ℓ (shiftGerm ℓ H)=(z:Padic ℓ)^(-(ℓ:ℤ))*
      (S z ℓ H-(z:Padic ℓ)^ℓ*germEval ℓ H 1)) ∧
  (∀ H J : Germ ℓ,S z ℓ (H+J)=S z ℓ H+S z ℓ J) ∧
  (∀ (a : PadicInt ℓ) (H : Germ ℓ),S z ℓ (a • H)=(a:Padic ℓ)*S z ℓ H) := by
  have hz1 : z≠1:=by
    intro h
    exact (rational_unit_of_norm ℓ (1-z) h1).1 (by rw [h,sub_self])
  refine ⟨li_shift z hz1,?_,S_summable z ℓ hz h1,
    fun H=>⟨S_integral z ℓ hz h1 H,S_shift z ℓ hz h1 H⟩,
    S_add z ℓ hz h1,S_smul z ℓ hz h1⟩
  intro j
  rw [←Rat.cast_pow,←liNeg_ratCast]
  exact li_integral z ℓ hz h1 j

def etaUnit (ℓ : ℕ) [Fact ℓ.Prime] (c : (PadicInt ℓ)ˣ) (j : ℕ) : PadicInt ℓ :=
  (j+1)*(-1)^j*((c⁻¹:((PadicInt ℓ)ˣ)):PadicInt ℓ)^(j+2)
noncomputable def E (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ) : Padic ℓ :=
  ∑' j : ℕ,(j+1:Padic ℓ)*(-(ℓ:Padic ℓ))^j*
    (c:Padic ℓ)^(-(j:ℤ)-2)*(liNeg j (z^ℓ):ℚ)
private theorem E_eq_S_eta (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ)
    (u : (PadicInt ℓ)ˣ) (hu : ((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ)) :
    E z ℓ c=S z ℓ (etaUnit ℓ u) := by
  have hinv : (((u⁻¹:(PadicInt ℓ)ˣ):PadicInt ℓ):Padic ℓ)=(c:Padic ℓ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←hu,←PadicInt.coe_mul]
    simp
  unfold E S
  apply tsum_congr
  intro j
  simp only [etaUnit,PadicInt.coe_mul,PadicInt.coe_add,PadicInt.coe_natCast,
    PadicInt.coe_neg,PadicInt.coe_one,PadicInt.coe_pow,hinv]
  rw [show -(j:ℤ)-2=-((j+2:ℕ):ℤ) by omega,_root_.zpow_neg,zpow_natCast,inv_pow,neg_pow]
  ring
private theorem etaScaled_eq_inverse (ℓ : ℕ) [Fact ℓ.Prime] (u : (PadicInt ℓ)ˣ) :
    germScaled ℓ (etaUnit ℓ u)=Port.Li2.affineInverseSeries u (ℓ:PadicInt ℓ) 2 := by
  apply PowerSeries.ext
  intro j
  simp only [germScaled,PowerSeries.coeff_mk,Port.Li2.affineInverseSeries,
    PowerSeries.coeff_C_mul,Port.Li2.inverseOneSubSeries,PowerSeries.coeff_rescale]
  simp only [PowerSeries.invOneSubPow,PowerSeries.coeff_mk]
  simp only [Nat.reduceAdd,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one,
    etaUnit]
  rw [mul_pow (-(ℓ:PadicInt ℓ)),neg_pow (ℓ:PadicInt ℓ) j,pow_add]
  ring
private theorem E_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (c : ℤ) (hc : ¬(ℓ:ℤ)∣c) :
    (∃ u : (PadicInt ℓ)ˣ,((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ) ∧
      E z ℓ c=S z ℓ (etaUnit ℓ u)) ∧ Intg ℓ (E z ℓ c) := by
  have hu : Unit ℓ ((c:ℚ):Padic ℓ):=by
    simpa only [Unit,Rat.cast_intCast,PadicInt.norm_def,PadicInt.coe_intCast] using (le_antisymm (PadicInt.norm_le_one (c:PadicInt ℓ))
      (le_of_not_gt (by rwa [PadicInt.norm_int_lt_one_iff_dvd])))
  have hv:=rational_unit_of_norm ℓ (c:ℚ) hu
  let u : (PadicInt ℓ)ˣ:=Port.Li2.integralRationalUnit (c:ℚ) hv.1 hv.2
  have he : ((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ):=by
    simp only [u,Port.Li2.integralRationalUnit_coe,Rat.cast_intCast]
  have hE:=E_eq_S_eta z ℓ c u he
  exact ⟨⟨u,he,hE⟩,by rw [hE]; exact S_integral z ℓ hz h1 (etaUnit ℓ u)⟩

private theorem E_eq_reciprocal (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (c : ℤ) (hc0 : (c:ℚ)≠0) (hcv : padicValRat ℓ (c:ℚ)=0) :
    E z ℓ c=(Port.Li2.padicParameterG (z^ℓ)
      (parameter_hypotheses z ℓ hz h1).2.2.1
      (Port.Li2.padicReciprocalSeries (c:ℚ) hc0 hcv 2):Padic ℓ) := by
  let u : (PadicInt ℓ)ˣ:=Port.Li2.integralRationalUnit (c:ℚ) hc0 hcv
  have hu : ((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ):=by
    simp only [u,Port.Li2.integralRationalUnit_coe,Rat.cast_intCast]
  rw [E_eq_S_eta z ℓ c u hu,S_eq_integral z ℓ hz h1,etaScaled_eq_inverse]
  rfl
private theorem reciprocal_congr (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) (h : a=b)
    (ha : a≠0) (hva : padicValRat ℓ a=0) (hb : b≠0) (hvb : padicValRat ℓ b=0) :
    Port.Li2.padicReciprocalSeries a ha hva 2=Port.Li2.padicReciprocalSeries b hb hvb 2 := by
  subst b
  rfl
private theorem E_shift (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (c : ℤ) (hc : ¬(ℓ:ℤ)∣c) :
    (z:Padic ℓ)^(c+ℓ)*E z ℓ (c+ℓ)=
      (z:Padic ℓ)^c*E z ℓ c-(z:Padic ℓ)^(c+ℓ)/(c+ℓ:Padic ℓ)^2 := by
  have hu : Unit ℓ ((c:ℚ):Padic ℓ):=by
    simpa only [Unit,Rat.cast_intCast,PadicInt.norm_def,PadicInt.coe_intCast] using
      (le_antisymm (PadicInt.norm_le_one (c:PadicInt ℓ))
        (le_of_not_gt (by rwa [PadicInt.norm_int_lt_one_iff_dvd])))
  have hv:=rational_unit_of_norm ℓ (c:ℚ) hu
  have hvc:=Port.Li2.rational_unit_add_prime_mul (p:=ℓ) (c:ℚ) hv.1 hv.2 1
  have hv0' : ((c+ℓ:ℤ):ℚ)≠0:=by simpa using hvc.1
  have hvv' : padicValRat ℓ ((c+ℓ:ℤ):ℚ)=0:=by simpa using hvc.2
  have hh:=parameter_hypotheses z ℓ hz h1
  have hs:=Port.Li2.padicParameterG_shift (z^ℓ) hh.2.1 hh.2.2.1 hh.2.2.2
    (pow_ne_zero ℓ hh.1) (Port.Li2.padicReciprocalSeries (c:ℚ) hv.1 hv.2 2)
    (Port.Li2.padicReciprocalSeries_isRestricted (c:ℚ) hv.1 hv.2 2) 1
  rw [Port.Li2.padicReciprocalSeries_shift] at hs
  have heval:=Port.Li2.padicReciprocalSeries_eval (p:=ℓ) (c:ℚ) hv.1 hv.2 2 1
  have hev : (Port.Li2.restrictedEval 1 (Port.Li2.padicReciprocalSeries (c:ℚ) hv.1 hv.2 2):Padic ℓ)=
      ((c:Padic ℓ)+(ℓ:Padic ℓ))⁻¹^2 := by
    have hi:=eq_inv_of_mul_eq_one_left heval
    simpa only [Rat.cast_intCast,PadicInt.coe_one,mul_one,inv_pow] using hi
  simp only [Nat.cast_one,Finset.sum_range_one,Nat.zero_add,pow_one,zero_add,
    PadicInt.coe_zero,Rat.cast_pow,mul_one] at hs
  have he0:=E_eq_reciprocal z ℓ hz h1 c hv.1 hv.2
  have he1:=E_eq_reciprocal z ℓ hz h1 (c+ℓ) hv0' hvv'
  have hdq : (c:ℚ)+(ℓ:ℚ)*((1:ℕ):ℚ)=((c+(ℓ:ℤ):ℤ):ℚ):=by push_cast;ring
  have he1' : E z ℓ (c+ℓ)=(Port.Li2.padicParameterG (z^ℓ) hh.2.2.1
      (Port.Li2.padicReciprocalSeries ((c:ℚ)+(ℓ:ℚ)*((1:ℕ):ℚ)) hvc.1 hvc.2 2):Padic ℓ):=by
    rw [reciprocal_congr ℓ _ _ hdq hvc.1 hvc.2 hv0' hvv']
    exact he1
  have hs' := hs
  simp only [Nat.cast_zero,zero_add] at hs'
  rw [←he0,←he1',hev] at hs'
  have hz0 : (z:Padic ℓ)≠0:=by exact_mod_cast hh.1
  have hb : (z:Padic ℓ)^ℓ*E z ℓ (c+ℓ)=
      E z ℓ c-(z:Padic ℓ)^ℓ/((c:Padic ℓ)+(ℓ:Padic ℓ))^2 := by
    have hh':=(eq_div_iff (pow_ne_zero ℓ hz0)).mp hs'
    rw [inv_pow] at hh'
    linear_combination hh'
  rw [_root_.zpow_add₀ hz0,zpow_natCast]
  linear_combination (z:Padic ℓ)^c*hb

noncomputable def T (z : ℚ) (ℓ j : ℕ) [Fact ℓ.Prime] : Padic ℓ :=
  (∑ b∈(Finset.Icc 1 j).filter (fun b=>¬ℓ∣b),(z:Padic ℓ)^b/(b:Padic ℓ)^2)+
    ∑ s : Fin ℓ,if j%ℓ≠s.val then
      (z:Padic ℓ)^((j:ℤ)-s.val)*E z ℓ ((j:ℤ)-s.val) else 0
private def residual (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ) : Padic ℓ :=
  if (ℓ:ℤ)∣c then 0 else (z:Padic ℓ)^c*E z ℓ c
private theorem residue_dvd_iff (j ℓ s : ℕ) (hs : s<ℓ) :
    (ℓ:ℤ)∣(j:ℤ)-s ↔ j%ℓ=s := by
  rw [←Int.modEq_iff_dvd]
  change (s:ℤ)%(ℓ:ℤ)=(j:ℤ)%(ℓ:ℤ) ↔ _
  rw [←Int.natCast_mod,←Int.natCast_mod,Int.natCast_inj,Nat.mod_eq_of_lt hs]
  exact eq_comm
private theorem T_residual (z : ℚ) (ℓ j : ℕ) [Fact ℓ.Prime] :
    T z ℓ j=(∑ b∈Finset.Icc 1 j,if ℓ∣b then 0 else (z:Padic ℓ)^b/(b:Padic ℓ)^2)+
      ∑ s∈Finset.range ℓ,residual z ℓ ((j:ℤ)-s) := by
  classical
  unfold T
  rw [Finset.sum_filter]
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    by_cases h : ℓ∣b <;> simp [h]
  · rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [residual,residue_dvd_iff j ℓ s.val s.isLt]
    by_cases h : j%ℓ=s.val <;> simp [h]
private theorem residual_step (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (c : ℤ) :
    residual z ℓ (c+ℓ)=residual z ℓ c-
      if (ℓ:ℤ)∣c then 0 else (z:Padic ℓ)^(c+ℓ)/(c+ℓ:Padic ℓ)^2 := by
  have hd : (ℓ:ℤ)∣c+ℓ ↔ (ℓ:ℤ)∣c:=dvd_add_self_right
  unfold residual
  simp only [hd]
  by_cases hc : (ℓ:ℤ)∣c
  · simp [hc]
  · simp only [if_neg hc]
    exact E_shift z ℓ hz h1 c hc

private theorem T_step (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (j : ℕ) (hj : 1≤j) :
    T z ℓ (j+1)=T z ℓ j := by
  classical
  let f : ℕ→Padic ℓ:=fun s=>residual z ℓ (((j+1:ℕ):ℤ)-s)
  let u : Padic ℓ:=if ℓ∣j+1 then 0 else (z:Padic ℓ)^(j+1)/(j+1:Padic ℓ)^2
  have hshift : (∑ s∈Finset.range ℓ,f (s+1))=
      ∑ s∈Finset.range ℓ,residual z ℓ ((j:ℤ)-s) := by
    apply Finset.sum_congr rfl
    intro s hs
    dsimp only [f]
    congr 1
    omega
  have hd : (ℓ:ℤ)∣((j+1:ℕ):ℤ)-ℓ ↔ ℓ∣j+1 := by
    rw [dvd_sub_self_right,Int.natCast_dvd_natCast]
  have hb:=residual_step z ℓ hz h1 (((j+1:ℕ):ℤ)-ℓ)
  rw [show ((j+1:ℕ):ℤ)-(ℓ:ℤ)+ℓ=((j+1:ℕ):ℤ) by omega] at hb
  simp only [hd,zpow_natCast] at hb
  simp only [Int.cast_sub,Int.cast_natCast,sub_add_cancel,Nat.cast_add,Nat.cast_one] at hb
  have hboundary : f 0=f ℓ-u:=by simpa only [f,u,Int.natCast_zero,sub_zero,Int.cast_add,Int.cast_one,Int.cast_natCast,Nat.cast_add,Nat.cast_one] using hb
  have hsum : (∑ s∈Finset.range ℓ,f s)=
      (∑ s∈Finset.range ℓ,residual z ℓ ((j:ℤ)-s))-u := by
    have ha:=Finset.sum_range_succ f ℓ
    have hc:=Finset.sum_range_succ' f ℓ
    rw [hshift] at hc
    linear_combination hc-ha+hboundary
  have htail : (∑ b∈Finset.Icc 1 (j+1),if ℓ∣b then (0:Padic ℓ) else (z:Padic ℓ)^b/(b:Padic ℓ)^2)=
      (∑ b∈Finset.Icc 1 j,if ℓ∣b then (0:Padic ℓ) else (z:Padic ℓ)^b/(b:Padic ℓ)^2)+u := by
    rw [Finset.sum_Icc_succ_top (by omega : 1≤j+1)]
    simp only [u,Nat.cast_add,Nat.cast_one]
  rw [T_residual,T_residual,htail]
  change _+(∑ s∈Finset.range ℓ,f s)=_
  rw [hsum]
  ring

private theorem T_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (j : ℕ) :
    Intg ℓ (T z ℓ j) := by
  rw [T_residual]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
    intro b hb
    split_ifs with hd
    · simp
    · have hb1 : ‖(b:Padic ℓ)‖=1:=by
        have hi : ‖(b:PadicInt ℓ)‖=1:=le_antisymm (PadicInt.norm_le_one _)
          (le_of_not_gt (by rwa [PadicInt.norm_natCast_lt_one_iff]))
        simpa only [PadicInt.norm_def,PadicInt.coe_natCast] using hi
      rw [norm_div,norm_pow,norm_pow,hz,hb1,one_pow,one_pow,div_self one_ne_zero]
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
    intro s hs
    unfold residual
    split_ifs with hd
    · simp
    · rw [norm_mul,norm_zpow,hz,one_zpow,one_mul]
      exact (E_integral z ℓ hz h1 ((j:ℤ)-s) hd).2
private theorem T_constant (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) :
    ∃ L : PadicInt ℓ,∀ j≥1,T z ℓ j=(L:Padic ℓ) := by
  let L : PadicInt ℓ:=⟨T z ℓ 1,T_integral z ℓ hz h1 1⟩
  refine ⟨L,?_⟩
  have he : ∀ k : ℕ,T z ℓ (k+1)=T z ℓ 1:=by
    intro k
    induction k with
    | zero=>rfl
    | succ k ih=>
      rw [T_step z ℓ hz h1 (k+1) (by omega)]
      exact ih
  intro j hj
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  exact he k
theorem regularization_constant (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) :
  (∀ c : ℤ,¬(ℓ:ℤ)∣c →
    (∃ u : (PadicInt ℓ)ˣ,((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ) ∧
      E z ℓ c=S z ℓ (etaUnit ℓ u)) ∧
    Intg ℓ (E z ℓ c) ∧
    (z:Padic ℓ)^(c+ℓ)*E z ℓ (c+ℓ)=
      (z:Padic ℓ)^c*E z ℓ c-(z:Padic ℓ)^(c+ℓ)/(c+ℓ:Padic ℓ)^2) ∧
  (∀ j≥1,T z ℓ (j+1)=T z ℓ j) ∧
  ∃ L : PadicInt ℓ,∀ j≥1,T z ℓ j=(L:Padic ℓ) := by
  refine ⟨?_,T_step z ℓ hz h1,T_constant z ℓ hz h1⟩
  intro c hc
  exact ⟨(E_integral z ℓ hz h1 c hc).1,(E_integral z ℓ hz h1 c hc).2,E_shift z ℓ hz h1 c hc⟩

noncomputable def localV (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (ξ : Padic ℓ) (F : RatFunc ℚ) : Padic ℓ :=
  (∑ j∈Finset.Icc 1 (pp F).natDegree,
    (j:Padic ℓ)*((pp F).coeff j:Padic ℓ)*(liNeg (j-1) (z^ℓ):ℚ))-
  ∑ m∈poleIndices F,(poleRes F m:Padic ℓ)*(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ))*
    ((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m:ℚ))
private theorem cast_power_inverse (z : ℚ) (ℓ m : ℕ) [Fact ℓ.Prime] :
    (((z^ℓ)^(-(m:ℤ)):ℚ):Padic ℓ)=(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ)) := by
  push_cast
  rw [←zpow_natCast,←zpow_mul]
  congr 1
  push_cast
  ring
private theorem localV_affine (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (ξ : Padic ℓ) (F : RatFunc ℚ) :
    localV z ℓ ξ F=(regularV (z^ℓ) F:ℚ)+
      (-(∑ m∈poleIndices F,(poleRes F m:Padic ℓ)*(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ))))*
        (ℓ:Padic ℓ)^2*ξ := by
  unfold localV regularV
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast]
  simp_rw [cast_power_inverse]
  let f : ℕ→Padic ℓ:=fun m=>(poleRes F m:Padic ℓ)*(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ))
  have he : (∑ m∈poleIndices F,f m*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m:ℚ)))=
      (∑ m∈poleIndices F,f m)*(ℓ:Padic ℓ)^2*ξ-
        ∑ m∈poleIndices F,f m*(tauK (z^ℓ) m:ℚ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [←mul_assoc,Finset.sum_mul]
  change _-(∑ m∈poleIndices F,f m*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m:ℚ)))=_
  rw [he]
  dsimp only [f]
  simp only [Algebra.algebraMap_self_apply]
  ring
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
private theorem integer_fraction_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀ m∈S,m<ℓ) :
    let F:=rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)
    (∀ i,Intg ℓ ((pp F).coeff i:Padic ℓ)) ∧
    (∀ m∈poleIndices F,m<ℓ ∧ Intg ℓ (poleRes F m:Padic ℓ)) := by
  classical
  let F:=rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)
  have hc:=fraction_coefficients (P.map (Int.castRingHom ℚ)) S
  have hd : F.denom∣poleProd S:=RatFunc.denom_div_dvd _ _
  obtain ⟨hD,hI⟩:=canonical_poles F S hd
  have hsub : poleIndices F⊆S:=by rw [hI];exact Finset.filter_subset _ _
  constructor
  · intro i
    rw [hc.1]
    exact integer_quotient_coeff_integral ℓ P S i
  · intro m hm
    have he : poleRes F m=poleCoeff (P.map (Int.castRingHom ℚ)) S m:=by
      simpa only [if_pos hm] using hc.2 m (hsub hm)
    exact ⟨hS m (hsub hm),by rw [he];exact integer_poleCoeff_integral ℓ P S hS m (hsub hm)⟩
private theorem intg_mul {ℓ : ℕ} [Fact ℓ.Prime] {a b : Padic ℓ}
    (ha : Intg ℓ a) (hb : Intg ℓ b) : Intg ℓ (a*b) := by
  unfold Intg at *
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg b) hb
private theorem intg_sum {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*}
    (S : Finset ι) (f : ι→Padic ℓ) (hf : ∀ i∈S,Intg ℓ (f i)) :
    Intg ℓ (∑ i∈S,f i) :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) hf
private theorem nat_unit_norm (ℓ b : ℕ) [Fact ℓ.Prime] (hb : 0<b) (hbl : b<ℓ) :
    ‖(b:Padic ℓ)‖=1 := by
  have hd : ¬ℓ∣b:=by intro h;have he:=Nat.le_of_dvd hb h;omega
  have hi : ‖(b:PadicInt ℓ)‖=1:=le_antisymm (PadicInt.norm_le_one _)
    (le_of_not_gt (by rwa [PadicInt.norm_natCast_lt_one_iff]))
  simpa only [PadicInt.norm_def,PadicInt.coe_natCast] using hi
private theorem tau_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (m : ℕ) (hm : m<ℓ) :
    Intg ℓ ((tauK (z^ℓ) m:ℚ):Padic ℓ) := by
  simp only [tauK,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
  apply intg_sum
  intro b hb
  have hbi:=Finset.mem_Icc.mp hb
  unfold Intg
  rw [norm_div,norm_pow,norm_pow,norm_pow,hz,nat_unit_norm ℓ b (by omega) (by omega)]
  norm_num
private theorem regularV_integral_of_coefficients (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (F : RatFunc ℚ)
    (hP : ∀ i,Intg ℓ ((pp F).coeff i:Padic ℓ))
    (hR : ∀ m∈poleIndices F,m<ℓ ∧ Intg ℓ (poleRes F m:Padic ℓ)) :
    Intg ℓ ((regularV (z^ℓ) F:ℚ):Padic ℓ) := by
  simp only [regularV,Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,
    Algebra.algebraMap_self_apply]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · apply intg_sum
    intro m hm
    apply intg_mul
    · apply intg_mul (hR m hm).2
      rw [cast_power_inverse]
      unfold Intg
      rw [norm_zpow,hz,one_zpow]
    · exact tau_integral z ℓ hz m (hR m hm).1
  · apply intg_sum
    intro j hj
    apply intg_mul
    · apply intg_mul
      · simpa only [Intg,PadicInt.norm_def,PadicInt.coe_natCast] using PadicInt.norm_le_one (j:PadicInt ℓ)
      · exact hP j
    · exact li_integral z ℓ hz h1 (j-1)

private theorem localV_fraction_integral_affine (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀ m∈S,m<ℓ) :
    let F:=rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)
    ∃ a b : PadicInt ℓ,(a:Padic ℓ)=(regularV (z^ℓ) F:ℚ) ∧
      ∀ ξ : Padic ℓ,localV z ℓ ξ F=(a:Padic ℓ)+(b:Padic ℓ)*(ℓ:Padic ℓ)^2*ξ := by
  let F:=rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)
  have hi:=integer_fraction_integral ℓ P S hS
  have ha : Intg ℓ ((regularV (z^ℓ) F:ℚ):Padic ℓ):=
    regularV_integral_of_coefficients z ℓ hz h1 F hi.1 hi.2
  let B : Padic ℓ:=-(∑ m∈poleIndices F,(poleRes F m:Padic ℓ)*(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ)))
  have hb : Intg ℓ B:=by
    unfold B Intg
    rw [norm_neg]
    apply intg_sum
    intro m hm
    apply intg_mul (hi.2 m hm).2
    unfold Intg
    rw [norm_zpow,hz,one_zpow]
  refine ⟨⟨_,ha⟩,⟨B,hb⟩,rfl,?_⟩
  intro ξ
  exact localV_affine z ℓ ξ F
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
private theorem tauK_ratCast (m : ℕ) (w : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    ((tauK w m:ℚ):Padic ℓ)=tauK (w:Padic ℓ) m := by
  unfold tauK
  push_cast
  rfl
private theorem regularV_ratCast (w : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) :
    ((regularV w F:ℚ):Padic ℓ)=regularV (w:Padic ℓ) F := by
  unfold regularV
  simp only [Algebra.algebraMap_self_apply,eq_ratCast,Rat.cast_add,
    Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,Rat.cast_zpow]
  simp_rw [tauK_ratCast,liNeg_ratCast]
  simp only [Rat.cast_id]

theorem localV_integral_affine (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (A : TypeKey) (hc : A.c<ℓ) (e : ℕ) :
    ∃ a b : PadicInt ℓ,(a:Padic ℓ)=(regularV (z^ℓ) (rfX^e*weight A):Padic ℓ) ∧
      ∀ ξ : Padic ℓ,localV z ℓ ξ (rfX^e*weight A)=
        (a:Padic ℓ)+(b:Padic ℓ)*(ℓ:Padic ℓ)^2*ξ := by
  have hS : ∀ m∈poleSet A,m<ℓ:=by
    intro m hm
    cases hk : A.kind <;> simp only [poleSet,hk,Finset.mem_Ico,Finset.mem_Ioc] at hm <;> omega
  rw [weight_fraction]
  simpa only [regularV_ratCast,Rat.cast_pow] using localV_fraction_integral_affine z ℓ hz h1 ((X:ℤ[X])^e*weightNumInt A) (poleSet A) hS

noncomputable def localClass (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : Fin ℓ) (ξ : Padic ℓ) (F : RatFunc ℚ) : Padic ℓ :=
  (z:Padic ℓ)^(-(s:ℤ))*
    (∑ i∈Finset.range (((X*pp F).derivative.comp
      (C (-(s:ℚ))+C (ℓ:ℚ)*X)).natDegree+1),
      (((X*pp F).derivative.comp (C (-(s:ℚ))+C (ℓ:ℚ)*X)).coeff i:Padic ℓ)*
        (liNeg i (z^ℓ):ℚ))+
  ∑ j∈poleIndices F,(poleRes F j:Padic ℓ)*(j:Padic ℓ)*
    if j%ℓ=s.val then
      (z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
        ((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) (j/ℓ):ℚ))
    else (z:Padic ℓ)^(-(s:ℤ))*E z ℓ ((j:ℤ)-s.val)

#print axioms li_shift_and_germ
#print axioms regularization_constant
#print axioms localV_integral_affine
end
end CatalanCore.Li2.NV





