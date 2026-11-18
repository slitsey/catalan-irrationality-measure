module
public import CatalanCore.Li2.NVMod.Formula
public import CatalanCore.Li2.NVMod.ModValue
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

theorem RFValue.polylog {K : Type*} [Field K] {φ : ℤ[X]→+*K} {r : K}
    (hX : RFValue φ rfX r) (h1 : r≠1) (j : ℕ) : RFValue φ (liNeg j rfX) (liNeg j r) := by
  have hden : (1:K)-r≠0 := sub_ne_zero.mpr h1.symm
  have hone : RFValue φ (1:RatFunc ℚ) (1:K) := by simpa using RFValue.nat φ 1
  by_cases hj : j=0
  · simp only [liNeg,if_pos hj]
    exact hX.div (hone.sub hX) hden
  · simp only [liNeg,if_neg hj]
    apply RFValue.sum
    intro i hi
    exact (((RFValue.nat φ (Nat.stirlingSecond j i)).mul (RFValue.nat φ i.factorial)).mul
      (hX.pow i)).div ((hone.sub hX).pow (i+1)) (pow_ne_zero _ hden)

theorem RFValue.polylog_sum {K : Type*} [Field K] {φ : ℤ[X]→+*K} {r : K}
    (hX : RFValue φ rfX r) (h1 : r≠1) (P : ℤ[X]) :
    RFValue φ
      ((P.map (Int.castRingHom ℚ)).sum (fun k c=>(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) c*liNeg (k-1) rfX))
      ((P.map (Int.castRingHom K)).sum (fun k c=>(k:K)*c*liNeg (k-1) r)) := by
  classical
  rw [Polynomial.sum_over_range' _ (by intro k;simp) (P.natDegree+1)
      ((Polynomial.natDegree_map_le).trans_lt (Nat.lt_succ_self _)),
    Polynomial.sum_over_range' _ (by intro k;simp) (P.natDegree+1)
      ((Polynomial.natDegree_map_le).trans_lt (Nat.lt_succ_self _))]
  apply RFValue.sum
  intro k hk
  simp only [Polynomial.coeff_map,Int.coe_castRingHom]
  have hc := RFValue.int φ (P.coeff k)
  have hterm := ((RFValue.nat φ k).mul hc).mul (hX.polylog h1 (k-1))
  simpa only [eq_ratCast,map_intCast,Rat.cast_intCast] using hterm

theorem map_eval_int (K : Type*) [Field K] (P : ℤ[X]) (x : ℤ) :
    (P.map (Int.castRingHom K)).eval (x:K)=((P.eval x:ℤ):K) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply _ _

theorem numeratorK_eval_int (K : Type*) [Field K] (A : TypeKey) (e m : ℕ) :
    (X^e*numeratorK K A).eval (-(m:K))=(((X^e*numeratorZ A).eval (-(m:ℤ)):ℤ):K) := by
  have he : (X^e*numeratorK K A)=(X^e*numeratorZ A).map (Int.castRingHom K) := by
    simp [Polynomial.map_mul,Polynomial.map_pow,numeratorZ_map]
  rw [he]
  simpa only [Int.cast_neg,Int.cast_natCast] using map_eval_int K (X^e*numeratorZ A) (-(m:ℤ))

theorem denominatorK_deriv_eval_int (K : Type*) [Field K] (A : TypeKey) (m : ℕ) :
    (denominatorK K A).derivative.eval (-(m:K))=(((denominatorZ A).derivative.eval (-(m:ℤ)):ℤ):K) := by
  rw [←denominatorZ_map K A,Polynomial.derivative_map]
  simpa only [Int.cast_neg,Int.cast_natCast] using map_eval_int K (denominatorZ A).derivative (-(m:ℤ))

theorem denominatorK_deriv_pole (K : Type*) [Field K] (A : TypeKey) (m : ℕ) (hm : m∈poles A) :
    (denominatorK K A).derivative.eval (-(m:K))=∏ n∈(poles A).erase m,((n:K)-m) := by
  have he : denominatorK K A=(X+C (m:K))*(∏ n∈(poles A).erase m,(X+C (n:K))) :=
    (Finset.mul_prod_erase _ _ hm).symm
  rw [he]
  simp [Polynomial.derivative_mul,Polynomial.eval_prod,sub_eq_add_neg,add_comm]

theorem goodFormulaPrime_deriv_ne (A : TypeKey) (p : ℕ) [Fact p.Prime]
    (hp : goodFormulaPrime A p) (m : ℕ) (hm : m∈poles A) :
    (denominatorK (ZMod p) A).derivative.eval (-(m:ZMod p))≠0 := by
  rw [denominatorK_deriv_pole _ A m hm]
  apply Finset.prod_ne_zero_iff.mpr
  intro n hn
  obtain ⟨hnm,hn⟩ := Finset.mem_erase.mp hn
  apply sub_ne_zero.mpr
  intro he
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (hp.2 n hn),ZMod.val_natCast_of_lt (hp.2 m hm)] at hv
  exact hnm hv

theorem residueK_Q (A : TypeKey) (e m : ℕ) :
    residueK ℚ A e m=residue A m*(X^e:ℚ[X]).eval (-(m:ℚ)) := by
  simp only [residueK,numeratorK_Q,denominatorK_Q,residue,Polynomial.eval_mul]
  ring

theorem residue_value (A : TypeKey) (p : ℕ) [Fact p.Prime]
    (φ : ℤ[X]→+*ZMod p) (hp : goodFormulaPrime A p) (e m : ℕ) (hm : m∈poles A) :
    RFValue φ (algebraMap ℚ (RatFunc ℚ) (residue A m*(X^e:ℚ[X]).eval (-(m:ℚ))))
      (residueK (ZMod p) A e m) := by
  have hd : (((denominatorZ A).derivative.eval (-(m:ℤ)):ℤ):ZMod p)≠0 := by
    rw [←denominatorK_deriv_eval_int]
    exact goodFormulaPrime_deriv_ne A p hp m hm
  rw [←residueK_Q A e m]
  simp only [residueK,numeratorK_eval_int,denominatorK_deriv_eval_int,map_div₀,map_intCast]
  exact (RFValue.int φ _).div (RFValue.int φ _) hd

theorem rfPoly_C_rat (q : ℚ) : rfPoly (C q)=(q:RatFunc ℚ) := by
  simpa [rfPoly,eq_ratCast] using (RatFunc.algebraMap_apply (K:=ℚ) q).symm

theorem natCast_zmod_ne_zero_lt (p n : ℕ) (hn : 0<n) (hp : n<p) : (n:ZMod p)≠0 := by
  intro hz
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hp,ZMod.val_zero] at hv
  omega

theorem omega_value (p : ℕ) [Fact p.Prime] (φ : ℤ[X]→+*ZMod p) (r : ZMod p)
    (hX : RFValue φ rfX r) (hr : r≠0) (m : ℕ) (hm : m<p) :
    RFValue φ (omegaRF m) ((r^m)⁻¹*formulaTau (ZMod p) r m) := by
  have hs : RFValue φ (omegaRF m)
      (∑ b∈Icc 1 m,r^((b:ℤ)-m)/(b:ZMod p)^2) := by
    unfold omegaRF
    apply RFValue.sum
    intro b hb
    have hbr := Finset.mem_Icc.mp hb
    have hb0 : (b:ZMod p)≠0 := natCast_zmod_ne_zero_lt p b (by omega) (by omega)
    have hh := (hX.zpow hr ((b:ℤ)-m)).div ((RFValue.nat φ b).pow 2) (pow_ne_zero _ hb0)
    simpa only [rfPoly_C_rat,Rat.cast_pow,Rat.cast_natCast] using hh
  have he : (∑ b∈Icc 1 m,r^((b:ℤ)-m)/(b:ZMod p)^2)=(r^m)⁻¹*formulaTau (ZMod p) r m := by
    rw [formulaTau,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [zpow_sub₀ hr,zpow_natCast,zpow_natCast]
    ring
  rw [he] at hs
  exact hs

theorem rational_polylog_Icc (P : ℚ[X]) :
    P.sum (fun k c=>(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) c*liNeg (k-1) rfX)=
      ∑ k∈Icc 1 P.natDegree,(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) (P.coeff k)*liNeg (k-1) rfX := by
  classical
  rw [Polynomial.sum_over_range _ (by intro k;simp)]
  have hs : range (P.natDegree+1)=insert 0 (Icc 1 P.natDegree) := by
    ext k
    simp only [mem_range,mem_insert,mem_Icc]
    omega
  rw [hs,Finset.sum_insert (by simp)]
  simp

theorem momentRF_positive_sum (A : TypeKey) (e : ℕ) :
    momentRF A (X^e)=
      (polyPart A (X^e)).sum (fun k c=>(k:RatFunc ℚ)*algebraMap ℚ (RatFunc ℚ) c*liNeg (k-1) rfX)+
      ∑ m∈(poles A).filter (0<·),
        algebraMap ℚ (RatFunc ℚ) (residue A m*(X^e:ℚ[X]).eval (-(m:ℚ)))*omegaRF m := by
  rw [rational_polylog_Icc,momentRF_partial_fractions,poles_eq_poleSet]
  rw [add_comm]
  simp only [eq_ratCast,map_ratCast]
  congr 1 <;> try rfl
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hpos : 0<m
  · rw [if_pos hpos]
  · have hm0 : m=0 := by omega
    subst m
    simp [omegaRF]

theorem momentFormula_sum (K : Type*) [Field K] (A : TypeKey) (r : K) (e : ℕ) :
    momentFormula K A r e=
      (quotientK K A e).sum (fun k c=>(k:K)*c*liNeg (k-1) r)+
      ∑ m∈(poles A).filter (0<·),residueK K A e m*(r^m)⁻¹*formulaTau K r m := by
  unfold momentFormula
  rw [Polynomial.sum_over_range _ (by intro k;simp)]
  simp only [formulaLiNeg_eq]

theorem moment_value (A : TypeKey) (p : ℕ) [Fact p.Prime]
    (φ : ℤ[X]→+*ZMod p) (hp : goodFormulaPrime A p) (r : ZMod p)
    (hX : RFValue φ rfX r) (hr : r≠0) (h1 : r≠1) (e : ℕ) :
    RFValue φ (momentRF A (X^e)) (momentFormula (ZMod p) A r e) := by
  rw [momentRF_positive_sum,momentFormula_sum]
  apply RFValue.add
  · have hh := hX.polylog_sum h1 (quotientZ A e)
    rw [quotientZ_map,quotientZ_map,quotientK_Q] at hh
    exact hh
  · apply RFValue.sum
    intro m hm
    have hmem := (Finset.mem_filter.mp hm).1
    have hc := residue_value A p φ hp e m hmem
    have hw := omega_value p φ r hX hr m (hp.2 m hmem)
    simpa only [mul_assoc] using hc.mul hw

theorem moment_formula_mod (I : EndpointInput) [Fact I.p.Prime]
    (hp : goodFormulaPrime I.key I.p) (r : ZMod I.p) (hr : r≠0) (h1 : r≠1)
    (i j : Fin I.key.size) :
    ((I.mz (i.val+j.val)).map (Int.castRingHom (ZMod I.p))).eval r=
      (I.D:ZMod I.p)*r^I.clearZ*(1-r)^I.clearOne*
        momentFormula (ZMod I.p) I.key r (i.val+j.val) := by
  let φ : ℤ[X]→+*ZMod I.p := Polynomial.eval₂RingHom (Int.castRingHom (ZMod I.p)) r
  have hx : RFValue φ rfX r := by
    simpa only [φ,intPolyRF,Polynomial.map_X,rfX,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X] using RFValue.intPoly φ X
  have hone : RFValue φ (1:RatFunc ℚ) (1:ZMod I.p) := by simpa using RFValue.nat φ 1
  have hD : RFValue φ (rfPoly (C (I.D:ℚ))) (I.D:ZMod I.p) := by
    simpa only [rfPoly_C_rat,Rat.cast_natCast] using RFValue.nat φ I.D
  have hm := moment_value I.key I.p φ hp r hx hr h1 (i.val+j.val)
  have hv := ((hD.mul (hx.pow I.clearZ)).mul ((hone.sub hx).pow I.clearOne)).mul hm
  have hz := RFValue.intPoly φ (I.mz (i.val+j.val))
  rw [I.moment_clear] at hz
  have he := hz.unique hv
  simpa only [φ,Polynomial.coe_eval₂RingHom,Polynomial.eval_map] using he


#print axioms moment_value
#print axioms moment_formula_mod
end
end CatalanCore.Li2.NVMod

