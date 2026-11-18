module
public import CatalanCore.Li2.NV.Constants
public import CatalanCore.Li2.NV.Binomial
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
noncomputable section
variable {K : Type*} [Field K]
private def bt (r i : ℕ) (y : K) : K := (Nat.choose r i:K)*y^i*(1-y)^(r-i)
private theorem bt_above (r i : ℕ) (y : K) (hi:r < i) : bt r i y=0 := by
  simp [bt,Nat.choose_eq_zero_of_lt hi]
private theorem bt_step (r j : ℕ) (y : K) (hj:j≤r) :
    bt (r+1) (j+1) y-bt r (j+1) y=y*(bt r j y-bt r (j+1) y) := by
  by_cases he:j=r
  · subst j
    simp [bt,Nat.choose_eq_zero_of_lt (Nat.lt_succ_self r),pow_succ] <;> ring
  · have hjr:j<r:=lt_of_le_of_ne hj he
    have hsub:r-j=(r-(j+1))+1:=by omega
    unfold bt
    rw [Nat.choose_succ_succ,Nat.cast_add]
    simp only [Nat.add_sub_add_right]
    rw [hsub,pow_succ,pow_succ]
    ring
private theorem tail_step (r t : ℕ) (y : K) (ht:t≤r) :
    BinTail (r+1) t y-BinTail r t y=y*bt r t y := by
  have tel (f:ℕ→K) : ∀ b,t≤b →
      (∑ i∈Ioc t b,(f (i-1)-f i))=f t-f b := by
    intro b hb
    induction b,hb using Nat.le_induction with
    | base => simp
    | succ b hb ih => rw [Finset.sum_Ioc_succ_top hb,ih];simp <;> ring
  have hterms : (∑ i∈Ioc t (r+1),(bt (r+1) i y-bt r i y))=
      y*(bt r t y-bt r (r+1) y) := by
    calc
      _ = ∑ i∈Ioc t (r+1),y*(bt r (i-1) y-bt r i y) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi0 : i≠0:=by have h: t < i := (Finset.mem_Ioc.mp hi).1;omega
        obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hi0
        simpa using bt_step r j y (by have h:= (Finset.mem_Ioc.mp hi).2;omega)
      _ = _ := by rw [← Finset.mul_sum,tel (fun j => bt r j y) (r+1) (by omega)]
  rw [Finset.sum_sub_distrib,Finset.sum_Ioc_succ_top ht (fun i=>bt r i y),bt_above r (r+1) y (by omega),add_zero,sub_zero] at hterms
  exact hterms

theorem pascal_and_pair_generic (r t : ℕ) (ht : t+4≤r) (y : K) :
  BinTail (r+1) (t+4) y-BinTail r t y =
    (Nat.choose r t:K)*y^(t+1)*(1-y)^(r-t)-
      ∑ e∈Finset.Icc 1 4, (Nat.choose (r+1) (t+e):K)*y^(t+e)*(1-y)^(r+1-t-e) := by
  have hs:=tail_step r t y (by omega)
  have hc:=Finset.sum_Ioc_consecutive (fun i=>bt (r+1) i y)
    (by omega : t≤t+4) (by omega : t+4≤r+1)
  have hi : Ioc t (t+4)={t+1,t+2,t+3,t+4} := by ext i;simp;omega
  have he : Icc 1 4=({1,2,3,4}:Finset ℕ) := by decide
  have hsmall : (∑ i∈Ioc t (t+4),bt (r+1) i y)=
      ∑ e∈Icc 1 4,(Nat.choose (r+1) (t+e):K)*y^(t+e)*(1-y)^(r+1-t-e) := by
    rw [hi,he]
    simp [bt,Nat.sub_sub] <;> ring
  change _+BinTail (r+1) (t+4) y=BinTail (r+1) t y at hc
  rw [hsmall] at hc
  have hb : y*bt r t y=(Nat.choose r t:K)*y^(t+1)*(1-y)^(r-t) := by simp only [bt,pow_succ];ring
  rw [hb] at hs
  calc
    _ = (BinTail (r+1) t y-BinTail r t y)-
        ∑ e∈Finset.Icc 1 4,(Nat.choose (r+1) (t+e):K)*y^(t+e)*(1-y)^(r+1-t-e) := by
      rw [← hc]
      ring
    _ = _ := by rw [hs]
theorem pascal_and_pair (r t : ℕ) (ht : t+4≤r) (y : ℚ) :
  BinTail (r+1) (t+4) y-BinTail r t y =
    (Nat.choose r t:ℚ)*y^(t+1)*(1-y)^(r-t)-
      ∑ e∈Finset.Icc 1 4,(Nat.choose (r+1) (t+e):ℚ)*y^(t+e)*(1-y)^(r+1-t-e) :=
  pascal_and_pair_generic r t ht y
/-- The finite four-step binomial coefficient numerator. -/
def pairNumerator {R : Type*} [CommRing R] (r t y : R) : R :=
  (t+1)*(t+2)*(t+3)*(t+4)*(1-y)^3-
  (r+1)*(t+2)*(t+3)*(t+4)*(1-y)^3-
  (r+1)*(r-t)*(t+3)*(t+4)*y*(1-y)^2-
  (r+1)*(r-t)*(r-t-1)*(t+4)*y^2*(1-y)-
  (r+1)*(r-t)*(r-t-1)*(r-t-2)*y^3

/-- After the residue relation t=4r, the cubic obstruction is exactly the
four-step numerator. No characteristic or numerical prime is fixed. -/
theorem pair_numerator_identity {R : Type*} [CommRing R] (r y : R) :
    y*pairNumerator r (4*r) y=(r+1)*(pairPoly y).eval r := by
  simp only [pairNumerator,pairPoly,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
  ring


private theorem four_choose_ratios (r t : ℕ) (ht : t+4≤r)
    (h1 : (t+1:K)≠0) (h2 : (t+2:K)≠0) (h3 : (t+3:K)≠0) (h4 : (t+4:K)≠0) :
    (Nat.choose (r+1) (t+1):K)=(Nat.choose r t:K)*(r+1:K)/(t+1:K) ∧
    (Nat.choose (r+1) (t+2):K)=(Nat.choose r t:K)*(r+1:K)*(r-t:K)/((t+1:K)*(t+2:K)) ∧
    (Nat.choose (r+1) (t+3):K)=(Nat.choose r t:K)*(r+1:K)*(r-t:K)*(r-t-1:K)/((t+1:K)*(t+2:K)*(t+3:K)) ∧
    (Nat.choose (r+1) (t+4):K)=(Nat.choose r t:K)*(r+1:K)*(r-t:K)*(r-t-1:K)*(r-t-2:K)/
      ((t+1:K)*(t+2:K)*(t+3:K)*(t+4:K)) := by
  have he1 : (Nat.choose (r+1) (t+1):K)*(t+1:K)=(r+1:K)*(Nat.choose r t:K) := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using congrArg (fun n : ℕ=>(n:K))
      (Nat.add_one_mul_choose_eq r t).symm
  have hc1 : (Nat.choose (r+1) (t+1):K)=(Nat.choose r t:K)*(r+1:K)/(t+1:K) := by
    apply (eq_div_iff h1).mpr
    simpa only [mul_comm] using he1
  have step (e : ℕ) (he : e≤3) :
      (Nat.choose (r+1) (t+(e+1)):K)*(t+(e+1):K)=
        (Nat.choose (r+1) (t+e):K)*(r-t+1-e:K) := by
    have hc := congrArg (fun n : ℕ=>(n:K)) (Nat.choose_succ_right_eq (r+1) (t+e))
    have hs : r+1-(t+e)=(r-t)+1-e := by omega
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,hs,
      Nat.cast_sub (by omega : e≤r-t+1),Nat.cast_sub (by omega : t≤r)] at hc
    simpa only [Nat.add_assoc,Nat.cast_add,Nat.cast_one,add_assoc] using hc
  have hc2 : (Nat.choose (r+1) (t+2):K)=(Nat.choose r t:K)*(r+1:K)*(r-t:K)/((t+1:K)*(t+2:K)) := by
    have hh := step 1 (by omega)
    rw [hc1] at hh
    apply (eq_div_iff (mul_ne_zero h1 h2)).mpr
    field_simp at hh ⊢
    linear_combination hh
  have hc3 : (Nat.choose (r+1) (t+3):K)=(Nat.choose r t:K)*(r+1:K)*(r-t:K)*(r-t-1:K)/
      ((t+1:K)*(t+2:K)*(t+3:K)) := by
    have hh := step 2 (by omega)
    rw [hc2] at hh
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) h3)).mpr
    field_simp at hh ⊢
    linear_combination hh
  have hc4 : (Nat.choose (r+1) (t+4):K)=(Nat.choose r t:K)*(r+1:K)*(r-t:K)*(r-t-1:K)*(r-t-2:K)/
      ((t+1:K)*(t+2:K)*(t+3:K)*(t+4:K)) := by
    have hh := step 3 (by omega)
    rw [hc3] at hh
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4)).mpr
    field_simp at hh ⊢
    linear_combination hh
  exact ⟨hc1,hc2,hc3,hc4⟩
private theorem pair_tail_factor (r t : ℕ) (ht : t+4≤r) (y : K)
    (h1 : (t+1:K)≠0) (h2 : (t+2:K)≠0) (h3 : (t+3:K)≠0) (h4 : (t+4:K)≠0) :
    ((t+1:K)*(t+2:K)*(t+3:K)*(t+4:K))*(BinTail (r+1) (t+4) y-BinTail r t y)=
      (Nat.choose r t:K)*y^(t+1)*(1-y)^(r-t-3)*pairNumerator (r:K) (t:K) y := by
  have hc := four_choose_ratios r t ht h1 h2 h3 h4
  have hs : (∑ e∈Finset.Icc 1 4,(Nat.choose (r+1) (t+e):K)*y^(t+e)*(1-y)^(r+1-t-e))=
      (Nat.choose (r+1) (t+1):K)*y^(t+1)*(1-y)^(r+1-t-1)+
      (Nat.choose (r+1) (t+2):K)*y^(t+2)*(1-y)^(r+1-t-2)+
      (Nat.choose (r+1) (t+3):K)*y^(t+3)*(1-y)^(r+1-t-3)+
      (Nat.choose (r+1) (t+4):K)*y^(t+4)*(1-y)^(r+1-t-4) := by
    norm_num [show Finset.Icc 1 4=({1,2,3,4}:Finset ℕ) by decide] <;> ring
  have hp0 : (1-y)^(r-t)=(1-y)^(r-t-3)*(1-y)^3 := by rw [←pow_add] <;> (congr 1 <;> omega)
  have hp1 : (1-y)^(r+1-t-1)=(1-y)^(r-t-3)*(1-y)^3 := by rw [←pow_add] <;> (congr 1 <;> omega)
  have hp2 : (1-y)^(r+1-t-2)=(1-y)^(r-t-3)*(1-y)^2 := by rw [←pow_add] <;> (congr 1 <;> omega)
  have hp3 : (1-y)^(r+1-t-3)=(1-y)^(r-t-3)*(1-y) := by rw [←pow_succ] <;> (congr 1 <;> omega)
  have hp4 : (1-y)^(r+1-t-4)=(1-y)^(r-t-3) := by congr 1 <;> omega
  have hy2 : y^(t+2)=y^(t+1)*y := by rw [←pow_succ]
  have hy3 : y^(t+3)=y^(t+1)*y^2 := by rw [←pow_add] <;> (congr 1 <;> omega)
  have hy4 : y^(t+4)=y^(t+1)*y^3 := by rw [←pow_add] <;> (congr 1 <;> omega)
  rw [pascal_and_pair_generic r t ht y,hs,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,
    hp0,hp1,hp2,hp3,hp4,hy2,hy3,hy4]
  simp only [pairNumerator]
  field_simp <;> ring

private theorem tail_eq_pair_mod (ℓ r t : ℕ) [Fact ℓ.Prime]
    (hr : r+1<ℓ) (ht : t+4≤r) (y : ZMod ℓ) (hy0 : y≠0) (hy1 : y≠1)
    (hrel : (t:ZMod ℓ)=4*(r:ZMod ℓ))
    (htail : BinTail (r+1) (t+4) y-BinTail r t y=0) : (pairPoly y).eval (r:ZMod ℓ)=0 := by
  have hden (i : ℕ) (hi0 : 1 ≤ i) (hi4 : i ≤ 4) : (t+i:ZMod ℓ)≠0 := by
    rw [show (t+i:ZMod ℓ)=((t+i:ℕ):ZMod ℓ) by simp,ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hfac : (r.factorial:ZMod ℓ)≠0 := by
    rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by have hh:=Finset.mem_range.mp hi;omega)
  have hC : (Nat.choose r t:ZMod ℓ)≠0 := by
    have he : (Nat.choose r t:ZMod ℓ)*(t.factorial:ZMod ℓ)*((r-t).factorial:ZMod ℓ)=(r.factorial:ZMod ℓ) := by
      simpa only [Nat.cast_mul] using congrArg (fun n : ℕ=>(n:ZMod ℓ))
        (Nat.choose_mul_factorial_mul_factorial (by omega : t≤r))
    intro hzero
    rw [hzero,zero_mul,zero_mul] at he
    exact hfac he.symm
  have hn := pair_tail_factor r t ht y
    (by simpa only [Nat.cast_one] using hden 1 (by omega) (by omega))
    (by simpa only [Nat.cast_ofNat] using hden 2 (by omega) (by omega))
    (by simpa only [Nat.cast_ofNat] using hden 3 (by omega) (by omega))
    (by simpa only [Nat.cast_ofNat] using hden 4 (by omega) (by omega))
  rw [htail,mul_zero] at hn
  have hN : pairNumerator (r:ZMod ℓ) (t:ZMod ℓ) y=0 :=
    (mul_eq_zero.mp hn.symm).resolve_left
      (mul_ne_zero (mul_ne_zero hC (pow_ne_zero _ hy0)) (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hy1))))
  have hp := pair_numerator_identity (r:ZMod ℓ) y
  rw [←hrel,hN,mul_zero] at hp
  have hR : (r:ZMod ℓ)+1≠0 := by
    rw [show (r:ZMod ℓ)+1=((r+1:ℕ):ZMod ℓ) by simp,ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hr
  exact (mul_eq_zero.mp hp.symm).resolve_left hR
private theorem tied_successor_parameters (n ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 13≤ℓ)
    (ht : tied n ℓ) (ht1 : tied (n+1) ℓ) :
    (n+1)/ℓ=n/ℓ ∧ k (n+1) ℓ=k n ℓ ∧ r (n+1) ℓ=r n ℓ+1 ∧
      r' (n+1) ℓ=r' n ℓ+4 ∧ r' n ℓ+4≤r n ℓ := by
  have hc := consecutive_tied n ℓ hℓ ht ht1
  refine ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,?_⟩
  have hh : r' (n+1) ℓ<r (n+1) ℓ := ht1
  rw [hc.2.2.1,hc.2.2.2] at hh
  omega
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
private theorem binTailInt_cast (ℓ : ℕ) [Fact ℓ.Prime] (r t : ℕ) (y : PadicInt ℓ) :
    (binTailInt ℓ r t y:Padic ℓ)=BinTail r t (y:Padic ℓ) := by
  change PadicInt.Coe.ringHom (binTailInt ℓ r t y)=_
  simp only [binTailInt,BinTail,map_sum,map_mul,map_pow,map_sub,map_one,map_natCast,
    PadicInt.Coe.ringHom_apply]
private theorem binTailInt_red (ℓ : ℕ) [Fact ℓ.Prime] (r t : ℕ) (y : PadicInt ℓ) :
    reduceInt ℓ (binTailInt ℓ r t y)=BinTail r t (reduceInt ℓ y) := by
  simp only [binTailInt,BinTail,map_sum,map_mul,map_pow,map_sub,map_one,map_natCast]

private theorem binomial_tails_eq_of_Vge (z a b : ℚ) (ℓ r t r1 t1 : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (hb : Unit ℓ (b:Padic ℓ))
    (h0 : Vge ℓ ((a-b*BinTail r t z⁻¹:ℚ):Padic ℓ) 1)
    (h1 : Vge ℓ ((a-b*BinTail r1 t1 z⁻¹:ℚ):Padic ℓ) 1) :
    BinTail r1 t1 (reduceInt ℓ (zInteger z ℓ hz))⁻¹=
      BinTail r t (reduceInt ℓ (zInteger z ℓ hz))⁻¹ := by
  have hn0 : ‖((a-b*BinTail r t z⁻¹:ℚ):Padic ℓ)‖≤(ℓ:ℝ)⁻¹ := by
    simpa only [Vge,Int.cast_one,Real.rpow_neg_one] using h0
  have hn1 : ‖((a-b*BinTail r1 t1 z⁻¹:ℚ):Padic ℓ)‖≤(ℓ:ℝ)⁻¹ := by
    simpa only [Vge,Int.cast_one,Real.rpow_neg_one] using h1
  have hn : ‖((a-b*BinTail r t z⁻¹:ℚ):Padic ℓ)-((a-b*BinTail r1 t1 z⁻¹:ℚ):Padic ℓ)‖≤(ℓ:ℝ)⁻¹ := by
    apply le_trans (by
      simpa only [sub_eq_add_neg,norm_neg] using
        IsUltrametricDist.norm_add_le_max ((a-b*BinTail r t z⁻¹:ℚ):Padic ℓ)
          (-((a-b*BinTail r1 t1 z⁻¹:ℚ):Padic ℓ)))
    simpa only [sub_eq_add_neg] using (max_le hn0 hn1)
  have he : ((a-b*BinTail r t z⁻¹:ℚ):Padic ℓ)-((a-b*BinTail r1 t1 z⁻¹:ℚ):Padic ℓ)=
      (b:Padic ℓ)*((BinTail r1 t1 z⁻¹:ℚ)-(BinTail r t z⁻¹:ℚ):Padic ℓ) := by
    push_cast
    ring
  rw [he,norm_mul,hb,one_mul] at hn
  have hcast (u v : ℕ) :
      (binTailInt ℓ u v (zInteger z ℓ hz).inv:Padic ℓ)=((BinTail u v z⁻¹:ℚ):Padic ℓ) := by
    rw [binTailInt_cast,coe_inv_of_unit ℓ _ (show ‖zInteger z ℓ hz‖=1 from hz)]
    simp only [BinTail,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_inv,
      Rat.cast_natCast,Rat.cast_one,zInteger]
  have hv : Vge ℓ ((binTailInt ℓ r1 t1 (zInteger z ℓ hz).inv:Padic ℓ)-
      (binTailInt ℓ r t (zInteger z ℓ hz).inv:Padic ℓ)) 1 := by
    simpa only [Vge,Int.cast_one,Real.rpow_neg_one,hcast] using hn
  have hh := reduce_eq_of_Vge ℓ (binTailInt ℓ r1 t1 (zInteger z ℓ hz).inv)
    (binTailInt ℓ r t (zInteger z ℓ hz).inv) hv
  change reduceInt ℓ (binTailInt ℓ r1 t1 (zInteger z ℓ hz).inv)=
    reduceInt ℓ (binTailInt ℓ r t (zInteger z ℓ hz).inv) at hh
  simpa only [binTailInt_red,reduce_inv_of_unit ℓ _ (show ‖zInteger z ℓ hz‖=1 from hz)] using hh

theorem pair_obstruction (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 13≤ℓ) (hR : Range n ℓ) (hR1 : Range (n+1) ℓ)
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (ht : tied n ℓ) (ht1 : tied (n+1) ℓ)
    (hc2 : Unit ℓ (c2 z (n/ℓ) (k n ℓ):Padic ℓ))
    (hT : Vge ℓ (Tprime z n ℓ:Padic ℓ) 1)
    (hT1 : Vge ℓ (Tprime z (n+1) ℓ:Padic ℓ) 1) :
  (pairPoly (reduceInt ℓ (zInteger z ℓ hz))⁻¹).eval (n%ℓ:ZMod ℓ)=0 := by
  have hp := tied_successor_parameters n ℓ hℓ ht ht1
  have hr : r n ℓ+1<ℓ := by rw [←hp.2.2.1];exact Nat.mod_lt (n+1) (Fact.out : ℓ.Prime).pos
  have htail := binomial_tails_eq_of_Vge z (c1 z (n/ℓ) (k n ℓ)) (c2 z (n/ℓ) (k n ℓ)) ℓ
    (r n ℓ) (r' n ℓ) (r n ℓ+1) (r' n ℓ+4) hz hc2
    (by simpa only [Tprime] using hT)
    (by simpa only [Tprime,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1] using hT1)
  let zI := zInteger z ℓ hz
  have hz0 : reduceInt ℓ zI≠0 := reduce_ne_zero_of_unit ℓ zI hz
  have h1I : Unit ℓ ((1-zI:PadicInt ℓ):Padic ℓ) := by
    simpa only [PadicInt.coe_sub,PadicInt.coe_one,zI,zInteger,Rat.cast_sub,Rat.cast_one] using h1
  have hz1 : reduceInt ℓ zI≠1 := by
    have hh := reduce_ne_zero_of_unit ℓ (1-zI) h1I
    intro he
    apply hh
    simp only [map_sub,map_one,he,sub_self]
  have hy0 : (reduceInt ℓ zI)⁻¹≠0 := inv_ne_zero hz0
  have hy1 : (reduceInt ℓ zI)⁻¹≠1 := by
    intro he
    have hh := mul_inv_cancel₀ hz0
    rw [he,mul_one] at hh
    exact hz1 hh
  have hrel : (r' n ℓ:ZMod ℓ)=4*(r n ℓ:ZMod ℓ) := by
    simp only [r',r,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_ofNat]
  simpa only [r,zI,ZMod.natCast_mod,ZMod.natCast_self,EuclideanDomain.mod_zero] using
    tail_eq_pair_mod ℓ (r n ℓ) (r' n ℓ) hr hp.2.2.2.2
      (reduceInt ℓ zI)⁻¹ hy0 hy1 hrel (sub_eq_zero.mpr htail)
#print axioms pair_obstruction
end
end CatalanCore.Li2.NV
