module
public import CatalanCore.Li2.NV.ReductionData
public import CatalanCore.Lai.NV7Dual
public import Mathlib.NumberTheory.Wilson
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped BigOperators Nat
namespace CatalanCore.Li2.NV
noncomputable section
private theorem coe_prod {ι : Type*} (ℓ : ℕ) [Fact ℓ.Prime]
    (S : Finset ι) (f : ι→PadicInt ℓ) :
    ((∏ i∈S,f i:PadicInt ℓ):Padic ℓ)=∏ i∈S,(f i:Padic ℓ) := by
  exact map_prod (PadicInt.Coe.ringHom : PadicInt ℓ→+*Padic ℓ) f S
private theorem nonmatching_difference_unit (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ)
    (j : ℕ) (hj : j%ℓ≠s.val) : ‖((j:PadicInt ℓ)-(s.val:PadicInt ℓ))‖=1 := by
  have hv := Port.Li2.nonmatching_rational_unit (p:=ℓ) s.val j s.isLt hj
  have hu : ‖(((j:ℚ)-s.val:ℚ):Padic ℓ)‖=1 := by
    rw [Padic.eq_padicNorm,padicNorm.eq_zpow_of_nonzero hv.1,hv.2]
    norm_num <;> ring
  simpa only [PadicInt.norm_def,PadicInt.coe_sub,PadicInt.coe_natCast,
    Rat.cast_sub,Rat.cast_natCast] using hu
private def nonmatchingInteger (N ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) : PadicInt ℓ :=
  ∏ i∈(Finset.Icc 1 N).filter (fun i=>i%ℓ≠s.val),((i:PadicInt ℓ)-(s.val:PadicInt ℓ))
private theorem nonmatchingInteger_unit (N ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    ‖nonmatchingInteger N ℓ s‖=1 := by
  rw [nonmatchingInteger,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact nonmatching_difference_unit ℓ s i (Finset.mem_filter.mp hi).2
private def piInteger (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) : PadicInt ℓ :=
  ∏ t∈Finset.univ.erase s,((t.val:PadicInt ℓ)-(s.val:PadicInt ℓ))^(m n ℓ t)
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
private def kappaInteger (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) : PadicInt ℓ :=
  nonmatchingInteger n ℓ s^3*(nonmatchingInteger (4*n) ℓ s).inv
private theorem kappaInteger_cast (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    (kappaInteger n ℓ s:Padic ℓ)=(kappaQ n ℓ s:Padic ℓ) := by
  rw [kappaInteger,PadicInt.coe_mul,PadicInt.coe_pow,
    coe_inv_of_unit ℓ _ (nonmatchingInteger_unit (4*n) ℓ s)]
  simp only [nonmatchingInteger,kappaQ,coe_prod,PadicInt.coe_sub,PadicInt.coe_natCast,
    Rat.cast_div,Rat.cast_prod,Rat.cast_pow,Rat.cast_sub,Rat.cast_natCast,
    Rat.cast_mul,Rat.cast_inv,Finset.prod_pow,div_eq_mul_inv]
private theorem piInteger_cast (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    (piInteger n ℓ s:Padic ℓ)=(((crtPi n ℓ s).eval (-(s:ℚ)):ℚ):Padic ℓ) := by
  simp only [piInteger,crtPi,crtPiInt,Polynomial.eval_map,Polynomial.eval_prod,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
    Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast,
    coe_prod,PadicInt.coe_pow,PadicInt.coe_sub,PadicInt.coe_add,PadicInt.coe_neg,PadicInt.coe_natCast,
    Rat.cast_prod,Rat.cast_pow,Rat.cast_add,Rat.cast_neg,Rat.cast_natCast,sub_eq_add_neg,add_comm]
private def uInteger (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (s : Fin ℓ) : PadicInt ℓ :=
  (if s.val=0 then 1 else -(s.val:PadicInt ℓ)*(zInteger z ℓ hz).inv^s.val)*
    kappaInteger n ℓ s*piInteger n ℓ s^2
private theorem uInteger_cast (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (s : Fin ℓ) :
    (uInteger z n ℓ hz s:Padic ℓ)=(uQ z n ℓ s:Padic ℓ) := by
  by_cases hs : s.val=0
  all_goals simp only [uInteger,uQ,hs,ite_true,ite_false,PadicInt.coe_mul,PadicInt.coe_pow,
    PadicInt.coe_neg,PadicInt.coe_natCast,PadicInt.coe_one,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_neg,Rat.cast_natCast,Rat.cast_one,Rat.cast_zpow]
  all_goals rw [kappaInteger_cast,piInteger_cast]
  · simp only [hs]
  · rw [coe_inv_of_unit ℓ _ (show ‖zInteger z ℓ hz‖=1 from hz)]
    simp [zInteger,_root_.zpow_neg,zpow_natCast]
private theorem redU_integer (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (R : ReductionData z n ℓ) (s : Fin ℓ) :
    redU R s=reduceInt ℓ (uInteger z n ℓ hz s) := by
  unfold redU
  congr 1
  apply PadicInt.ext
  rw [R.units_cast,uInteger_cast]
private theorem redU_product (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (R : ReductionData z n ℓ) (s : Fin ℓ) :
    redU R s=(if s.val=0 then 1 else -(s.val:ZMod ℓ)*
      (reduceInt ℓ (zInteger z ℓ hz))^(-(s.val:ℤ)))*
      (∏ i∈(Finset.Icc 1 n).filter (fun i=>i%ℓ≠s.val),((i:ZMod ℓ)-(s.val:ZMod ℓ)))^3 /
      (∏ i∈(Finset.Icc 1 (4*n)).filter (fun i=>i%ℓ≠s.val),((i:ZMod ℓ)-(s.val:ZMod ℓ))) *
      (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(m n ℓ t))^2 := by
  rw [redU_integer z n ℓ hz R s]
  simp only [uInteger,kappaInteger,map_mul,map_pow]
  rw [reduce_inv_of_unit ℓ _ (nonmatchingInteger_unit (4*n) ℓ s)]
  by_cases hs : s.val=0
  all_goals simp only [hs,ite_true,ite_false,map_mul,map_pow,map_one,map_neg,map_natCast,
    reduce_inv_of_unit ℓ _ (show ‖zInteger z ℓ hz‖=1 from hz),
    nonmatchingInteger,piInteger,map_prod,map_sub,_root_.zpow_neg,zpow_natCast,inv_pow,div_eq_mul_inv]
  all_goals ring
private theorem finite_field_prod_shift (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ)))=-1 := by
  classical
  have hz : (∏ t∈(Finset.univ:Finset (ZMod ℓ)).erase (s.val:ZMod ℓ),
      (t-(s.val:ZMod ℓ)))=-1 := by
    have hp : (-1:ZMod ℓ)^(ℓ-1)=1 := ZMod.pow_card_sub_one_eq_one (by norm_num)
    calc
      _ = ∏ t∈(Finset.univ:Finset (ZMod ℓ)).erase (s.val:ZMod ℓ),
          -((s.val:ZMod ℓ)-t) := by apply Finset.prod_congr rfl; intro t ht; ring
      _ = _ := by
        rw [Finset.prod_neg,Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ,ZMod.card,hp,CatalanCore.Lai.NV7.prod_erase_sub_zmod,one_mul]
  rw [←hz]
  refine Finset.prod_bij (fun t ht => (t.val:ZMod ℓ)) ?_ ?_ ?_ ?_
  · intro t ht
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro he
    have hh := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt s.isLt] at hh
    exact (Finset.mem_erase.mp ht).1 (Fin.ext hh)
  · intro t ht u hu he
    have hh := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt u.isLt] at hh
    exact Fin.ext hh
  · intro t ht
    let u : Fin ℓ := ⟨t.val,ZMod.val_lt t⟩
    refine ⟨u,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,?_⟩
    · intro he
      apply (Finset.mem_erase.mp ht).1
      calc
        t=(u.val:ZMod ℓ) := (ZMod.natCast_zmod_val t).symm
        _=(s.val:ZMod ℓ) := by rw [he]
    · exact ZMod.natCast_zmod_val t
  · intro t ht
    rfl
private theorem nonmatching_prod_group (N ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    (∏ i∈(Finset.Icc 1 N).filter (fun i => i%ℓ≠s.val),((i:ZMod ℓ)-(s.val:ZMod ℓ))) =
      ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(countClass N ℓ t) := by
  classical
  let residue : ℕ→Fin ℓ := fun i => ⟨i%ℓ,Nat.mod_lt i (Fact.out : ℓ.Prime).pos⟩
  have he := Finset.prod_fiberwise_of_maps_to
    (s := (Finset.Icc 1 N).filter (fun i => i%ℓ≠s.val)) (t := Finset.univ.erase s)
    (g := residue) (by
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_filter.mp hi).2 (congrArg Fin.val h))
    (fun i => (i:ZMod ℓ)-(s.val:ZMod ℓ))
  rw [←he]
  apply Finset.prod_congr rfl
  intro t ht
  have hts : t.val≠s.val := fun h => (Finset.mem_erase.mp ht).1 (Fin.ext h)
  have hf : ((Finset.Icc 1 N).filter (fun i => i%ℓ≠s.val)).filter (fun i => residue i=t)=
      (Finset.Icc 1 N).filter (fun i => i%ℓ=t.val) := by
    ext i
    simp only [Finset.mem_filter,residue,Fin.ext_iff]
    constructor
    · rintro ⟨⟨hi,hs⟩,ht⟩;exact ⟨hi,ht⟩
    · rintro ⟨hi,ht⟩;exact ⟨⟨hi,by rwa [ht]⟩,ht⟩
  rw [hf]
  calc
    _ = ∏ i∈(Finset.Icc 1 N).filter (fun i => i%ℓ=t.val),((t.val:ZMod ℓ)-(s.val:ZMod ℓ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      rw [←ZMod.natCast_mod i ℓ,hh]
    _ = _ := by simp only [Finset.prod_const,countClass]
private theorem grouped_scalar_simplify (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(a n ℓ t))^3 /
      (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(c n ℓ t)) *
      (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(m n ℓ t))^2 =
    ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(b n ℓ t) := by
  classical
  have he : (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(a n ℓ t))^3 /
      (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(c n ℓ t)) *
      (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(m n ℓ t))^2 =
      ∏ t∈Finset.univ.erase s,
        (((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(a n ℓ t))^3 /
        ((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(c n ℓ t) *
        (((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(m n ℓ t))^2 := by
    simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib,Finset.prod_pow]
  rw [he]
  apply Finset.prod_congr rfl
  intro t ht
  have hn : (t.val:ZMod ℓ)-(s.val:ZMod ℓ)≠0 := by
    intro h
    have hh := congrArg ZMod.val (sub_eq_zero.mp h)
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt s.isLt] at hh
    exact (Finset.mem_erase.mp ht).1 (Fin.ext hh)
  have hc := (class_counts n ℓ hR).1 t
  have hx : 3*a n ℓ t+2*m n ℓ t=c n ℓ t+b n ℓ t := by unfold m b; omega
  let v := (t.val:ZMod ℓ)-(s.val:ZMod ℓ)
  change (v^(a n ℓ t))^3/v^(c n ℓ t)*(v^(m n ℓ t))^2=v^(b n ℓ t)
  calc
    _ = (v^(3*a n ℓ t)*v^(2*m n ℓ t))/v^(c n ℓ t) := by
      simp only [pow_mul]
      ring
    _ = v^(3*a n ℓ t+2*m n ℓ t)/v^(c n ℓ t) := by rw [pow_add]
    _ = _ := by rw [hx,pow_add]; exact mul_div_cancel_left₀ _ (pow_ne_zero _ hn)
private theorem tied_b_counts (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (ht : tied n ℓ)
    (s : Fin ℓ) : b n ℓ s=if s.val∈Cset n ℓ then 3*(n/ℓ)+k n ℓ-1 else 3*(n/ℓ)+k n ℓ := by
  have hh := (class_counts n ℓ hR).2.2 s
  have ha := congrArg Prod.fst hh
  have hc := congrArg Prod.snd hh
  by_cases h0 : s.val=0
  · simp only [typeAC,h0,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
    simp only [b,h0,ha,hc,Cset,Finset.mem_Ioc,Nat.not_lt_zero,false_and,ite_false]
    omega
  · by_cases hr : s.val≤r n ℓ <;> by_cases hr' : s.val≤r' n ℓ <;>
      simp only [typeAC,h0,ne_eq,not_false_eq_true,true_and,hr,hr',ite_true,ite_false,Nat.add_zero] at ha hc
    all_goals simp only [b,ha,hc,Cset,Finset.mem_Ioc]
    all_goals unfold tied at ht
    all_goals split_ifs <;> omega
private theorem tied_scalar_product (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (ht : tied n ℓ) (s : Fin ℓ) :
    (∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(b n ℓ t)) =
      (-1:ZMod ℓ)^(3*(n/ℓ)+k n ℓ) /
        (∏ t∈Finset.univ.erase s,if t.val∈Cset n ℓ then ((t.val:ZMod ℓ)-(s.val:ZMod ℓ)) else 1) := by
  classical
  have hdiff : ∀ t∈Finset.univ.erase s,(t.val:ZMod ℓ)-(s.val:ZMod ℓ)≠0 := by
    intro t ht he
    have hh := congrArg ZMod.val (sub_eq_zero.mp he)
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt s.isLt] at hh
    exact (Finset.mem_erase.mp ht).1 (Fin.ext hh)
  have hd : r' n ℓ+ℓ*k n ℓ=4*r n ℓ := Nat.mod_add_div (4*(n%ℓ)) ℓ
  have hk : 1≤k n ℓ := by
    by_contra hn
    have hk0 : k n ℓ=0 := by omega
    rw [hk0,mul_zero,add_zero] at hd
    unfold tied at ht
    omega
  have hbeta : 1≤3*(n/ℓ)+k n ℓ := by omega
  have hden : (∏ t∈Finset.univ.erase s,
      if t.val∈Cset n ℓ then ((t.val:ZMod ℓ)-(s.val:ZMod ℓ)) else 1)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    split_ifs
    · exact hdiff t ht
    · exact one_ne_zero
  apply (eq_div_iff hden).mpr
  rw [←Finset.prod_mul_distrib]
  calc
    _ = ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(3*(n/ℓ)+k n ℓ) := by
      apply Finset.prod_congr rfl
      intro t ht'
      rw [tied_b_counts n ℓ hR ht t]
      by_cases hC : t.val∈Cset n ℓ
      · simp only [hC,ite_true]
        rw [←pow_succ,Nat.sub_add_cancel hbeta]
      · simp only [hC,ite_false,mul_one]
    _ = _ := by rw [Finset.prod_pow,finite_field_prod_shift]

private theorem redU_class_product (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (hR : Range n ℓ) (R : ReductionData z n ℓ) (s : Fin ℓ) :
    redU R s=(if s.val=0 then 1 else -(s.val:ZMod ℓ)*
      (reduceInt ℓ (zInteger z ℓ hz))^(-(s.val:ℤ)))*
      ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(b n ℓ t) := by
  rw [redU_product z n ℓ hz R s,nonmatching_prod_group n ℓ s,nonmatching_prod_group (4*n) ℓ s]
  let p : ZMod ℓ := if s.val=0 then 1 else -(s.val:ZMod ℓ)*
    (reduceInt ℓ (zInteger z ℓ hz))^(-(s.val:ℤ))
  let A := ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(a n ℓ t)
  let D := ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(c n ℓ t)
  let P := ∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(m n ℓ t)
  change p*A^3/D*P^2=p*(∏ t∈Finset.univ.erase s,((t.val:ZMod ℓ)-(s.val:ZMod ℓ))^(b n ℓ t))
  calc
    _=p*(A^3/D*P^2) := by ring
    _=_ := congrArg (fun y=>p*y) (grouped_scalar_simplify n ℓ hR s)
private theorem redU_tied_product (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (hR : Range n ℓ) (ht : tied n ℓ)
    (R : ReductionData z n ℓ) (s : Fin ℓ) :
    redU R s=(if s.val=0 then 1 else -(s.val:ZMod ℓ)*
      (reduceInt ℓ (zInteger z ℓ hz))^(-(s.val:ℤ)))*
      ((-1:ZMod ℓ)^(3*(n/ℓ)+k n ℓ) /
        (∏ t∈Finset.univ.erase s,if t.val∈Cset n ℓ then ((t.val:ZMod ℓ)-(s.val:ZMod ℓ)) else 1)) := by
  rw [redU_class_product z n ℓ hz hR R s,tied_scalar_product n ℓ hR ht s]
private theorem nat_factorial_nonzero_mod (ℓ d : ℕ) [Fact ℓ.Prime] (hd : d<ℓ) :
    (Nat.factorial d:ZMod ℓ)≠0 := by
  by_cases he : d=ℓ-1
  · rw [he,ZMod.wilsons_lemma]
    exact neg_ne_zero.mpr one_ne_zero
  · rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by have hh:=Finset.mem_range.mp hi;omega)
private theorem prod_prefix_factorial {F : Type*} [CommRing F] (d : ℕ) :
    (∏ i∈Finset.Ioc 0 d,(i:F))=(Nat.factorial d:F) := by
  have he : Finset.Ioc 0 d=Finset.Ico 1 (d+1) := by ext i;simp;omega
  rw [he,←Finset.prod_natCast,Finset.prod_Ico_id_eq_factorial]
private theorem prod_Ioc_factorial (ℓ a b : ℕ) [Fact ℓ.Prime] (hab : a≤b) (hb : b<ℓ) :
    (∏ i∈Finset.Ioc a b,(i:ZMod ℓ))=(Nat.factorial b:ZMod ℓ)/(Nat.factorial a:ZMod ℓ) := by
  have he := Finset.prod_Ioc_consecutive (fun i : ℕ=>(i:ZMod ℓ)) (Nat.zero_le a) hab
  rw [prod_prefix_factorial,prod_prefix_factorial] at he
  apply (eq_div_iff (nat_factorial_nonzero_mod ℓ a (lt_of_le_of_lt hab hb))).mpr
  rw [←he,mul_comm]
private theorem C_zero_product (n ℓ : ℕ) [Fact ℓ.Prime] (ht : tied n ℓ) (s0 : Fin ℓ)
    (hs0 : s0.val=0) :
    (∏ t∈Finset.univ.erase s0,
      if t.val∈Cset n ℓ then ((t.val:ZMod ℓ)-(s0.val:ZMod ℓ)) else 1) =
      (Nat.factorial (r n ℓ):ZMod ℓ)/(Nat.factorial (r' n ℓ):ZMod ℓ) := by
  classical
  simp only [hs0,Nat.cast_zero,sub_zero]
  rw [←Finset.prod_filter]
  have he : (∏ t∈(Finset.univ.erase s0).filter (fun t : Fin ℓ=>t.val∈Cset n ℓ),(t.val:ZMod ℓ))=
      ∏ i∈Finset.Ioc (r' n ℓ) (r n ℓ),(i:ZMod ℓ) := by
    refine Finset.prod_bij (fun t ht=>t.val) ?_ ?_ ?_ ?_
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · intro t ht u hu he
      exact Fin.ext he
    · intro i hi
      have hit := Finset.mem_Ioc.mp hi
      let t : Fin ℓ := ⟨i,lt_of_le_of_lt hit.2 (Nat.mod_lt n (Fact.out : ℓ.Prime).pos)⟩
      refine ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,hi⟩,rfl⟩
      intro he
      have hh := congrArg Fin.val he
      change i=s0.val at hh
      omega
    · intro t ht
      rfl
  rw [he]
  exact prod_Ioc_factorial ℓ (r' n ℓ) (r n ℓ) (Nat.le_of_lt ht)
    (Nat.mod_lt n (Fact.out : ℓ.Prime).pos)
private theorem prod_right_difference {F : Type*} [CommRing F] (s b : ℕ) (hsb : s≤b) :
    (∏ i∈Finset.Ioc s b,((i:F)-(s:F)))=(Nat.factorial (b-s):F) := by
  rw [←prod_prefix_factorial]
  refine Finset.prod_bij (fun i hi=>i-s) ?_ ?_ ?_ ?_
  · intro i hi
    have hh := Finset.mem_Ioc.mp hi
    simp only [Finset.mem_Ioc]
    omega
  · intro i hi j hj he
    have hi' := Finset.mem_Ioc.mp hi
    have hj' := Finset.mem_Ioc.mp hj
    omega
  · intro j hj
    have hh := Finset.mem_Ioc.mp hj
    refine ⟨s+j,Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro i hi
    exact (Nat.cast_sub (Nat.le_of_lt (Finset.mem_Ioc.mp hi).1)).symm
private theorem prod_left_difference {F : Type*} [CommRing F] (a s : ℕ) (has : a<s) :
    (∏ i∈Finset.Ioc a (s-1),((i:F)-(s:F)))=
      (-1:F)^(s-a-1)*(Nat.factorial (s-a-1):F) := by
  have he : (∏ i∈Finset.Ioc a (s-1),((i:F)-(s:F)))=
      ∏ i∈Finset.Ioc 0 (s-a-1),-(i:F) := by
    refine Finset.prod_bij (fun i hi=>s-i) ?_ ?_ ?_ ?_
    · intro i hi
      have hh := Finset.mem_Ioc.mp hi
      simp only [Finset.mem_Ioc]
      omega
    · intro i hi j hj he
      have hi' := Finset.mem_Ioc.mp hi
      have hj' := Finset.mem_Ioc.mp hj
      omega
    · intro j hj
      have hh := Finset.mem_Ioc.mp hj
      refine ⟨s-j,Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,by omega⟩
    · intro i hi
      have hh := Finset.mem_Ioc.mp hi
      rw [Nat.cast_sub (by omega : i≤s)]
      ring
  rw [he,Finset.prod_neg,prod_prefix_factorial,Nat.card_Ioc,Nat.sub_zero]

private theorem prod_interval_except {F : Type*} [CommRing F] (a b s : ℕ)
    (has : a<s) (hsb : s≤b) :
    (∏ i∈(Finset.Ioc a b).erase s,((i:F)-(s:F)))=
      (-1:F)^(s-a-1)*(Nat.factorial (s-a-1):F)*(Nat.factorial (b-s):F) := by
  have he : (Finset.Ioc a b).erase s=Finset.Ioc a (s-1) ∪ Finset.Ioc s b := by
    ext i
    simp only [Finset.mem_erase,Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc a (s-1)) (Finset.Ioc s b) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have hh := Finset.mem_Ioc.mp hi
    have hk := Finset.mem_Ioc.mp hj
    omega
  rw [he,Finset.prod_union hd,prod_left_difference a s has,prod_right_difference s b hsb]
private theorem C_difference_product {F : Type*} [CommRing F] (n ℓ : ℕ) [Fact ℓ.Prime]
    (s : Fin ℓ) :
    (∏ t∈Finset.univ.erase s,if t.val∈Cset n ℓ then ((t.val:F)-(s.val:F)) else 1) =
      ∏ i∈(Finset.Ioc (r' n ℓ) (r n ℓ)).erase s.val,((i:F)-(s.val:F)) := by
  classical
  rw [←Finset.prod_filter]
  refine Finset.prod_bij (fun t ht=>t.val) ?_ ?_ ?_ ?_
  · intro t ht
    have hh := Finset.mem_filter.mp ht
    exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hh.1).1 (Fin.ext he),hh.2⟩
  · intro t ht u hu he
    exact Fin.ext he
  · intro i hi
    have hit := Finset.mem_erase.mp hi
    have hb := Finset.mem_Ioc.mp hit.2
    let t : Fin ℓ := ⟨i,lt_of_le_of_lt hb.2 (Nat.mod_lt n (Fact.out : ℓ.Prime).pos)⟩
    refine ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,hit.2⟩,rfl⟩
    intro he
    exact hit.1 (congrArg Fin.val he)
  · intro t ht
    rfl
private theorem C_class_product (n ℓ : ℕ) [Fact ℓ.Prime] (ht : tied n ℓ)
    (s : Fin ℓ) (j : ℕ) (hs : s.val=r' n ℓ+1+j) (hj : j≤r n ℓ-r' n ℓ-1) :
    (∏ t∈Finset.univ.erase s,if t.val∈Cset n ℓ then ((t.val:ZMod ℓ)-(s.val:ZMod ℓ)) else 1) =
      (-1:ZMod ℓ)^j*(Nat.factorial j:ZMod ℓ)*(Nat.factorial (r n ℓ-r' n ℓ-1-j):ZMod ℓ) := by
  have htt : r' n ℓ<r n ℓ := ht
  rw [C_difference_product,prod_interval_except (r' n ℓ) (r n ℓ) s.val (by omega) (by omega)]
  have he1 : s.val-r' n ℓ-1=j := by omega
  have he2 : r n ℓ-s.val=r n ℓ-r' n ℓ-1-j := by omega
  rw [he1,he2]

theorem wilson_constants (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (hR : Range n ℓ) (ht : tied n ℓ)
    (R : ReductionData z n ℓ) (s0 : Fin ℓ) (hs0 : s0.val=0) :
  redU R s0=(-1:ZMod ℓ)^(3*(n/ℓ)+k n ℓ)*
      (Nat.factorial (r' n ℓ):ZMod ℓ)/(Nat.factorial (r n ℓ):ZMod ℓ) ∧
  ∀ (s : Fin ℓ) (j : ℕ), s.val=r' n ℓ+1+j → j≤r n ℓ-r' n ℓ-1 →
    redU R s=-(s.val:ZMod ℓ)*(reduceInt ℓ (zInteger z ℓ hz))^(-(s.val:ℤ))*
      (-1:ZMod ℓ)^(3*(n/ℓ)+k n ℓ+j)/
        ((Nat.factorial j:ZMod ℓ)*(Nat.factorial (r n ℓ-r' n ℓ-1-j):ZMod ℓ)) := by
  constructor
  · rw [redU_tied_product z n ℓ hz hR ht R s0,C_zero_product n ℓ ht s0 hs0]
    simp only [hs0,ite_true,one_mul,div_div_eq_mul_div]
  · intro s j hs hj
    have hsne : s.val≠0 := by omega
    rw [redU_tied_product z n ℓ hz hR ht R s,C_class_product n ℓ ht s j hs hj]
    simp only [hsne,ite_false,div_eq_mul_inv,_root_.mul_inv_rev,inv_pow,inv_neg_one,inv_neg,inv_one,pow_add]
    ring_nf
    norm_num <;> ring
#print axioms wilson_constants
end
end CatalanCore.Li2.NV
